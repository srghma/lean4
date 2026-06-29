// Lean compiler output
// Module: Lean.LibrarySuggestions.MePo
// Imports: Lean.LibrarySuggestions.Basic Lean.LibrarySuggestions.SymbolFrequency
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::{l_Float_ofScientific, lean_float_of_nat};
use crate::r#gen::Init::Prelude::{l_Array_extract___redArg, l_Lean_Name_append};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_append, l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_name, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Environment::l_Lean_Environment_constants;
use crate::r#gen::Lean::LibrarySuggestions::Basic::{
    initialize_Lean_LibrarySuggestions_Basic, l_Lean_LibrarySuggestions_isDeniedPremise,
    l_Lean_MVarId_getRelevantConstants, runtime_initialize_Lean_LibrarySuggestions_Basic,
};
use crate::r#gen::Lean::LibrarySuggestions::SymbolFrequency::{
    initialize_Lean_LibrarySuggestions_SymbolFrequency,
    l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg,
    runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_MessageData_paren, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::OriginalConstKind::l_Lean_wasOriginallyTheorem;
use crate::r#gen::Lean::Util::FoldConsts::l_Lean_Expr_getUsedConstantsAsSet;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::{
    lean_float_add, lean_float_decLe, lean_float_decLt, lean_float_div, lean_float_sub,
    lean_float_to_string,
};
use crate::ffi::lean_nat_shiftr;
use crate::ffi::lean_nat_log2;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 112, 111, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__0_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13053811699063877555 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__2_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__3_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__5_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10340502805995137493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 80, 111, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__7_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4818942117537471788 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__9_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15657238144179933357 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__10_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14640257312096924440 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__11_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8196988357891220159 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__12_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11902181847152380110 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__13_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__14_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5275749741163280611 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__15_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__16_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9216806068052575958 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__17_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__4_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14396443038400457343 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__18_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__6_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9244227521525129524 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__19_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__8_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12210201943900496225 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__20_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1610293474 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2621482290596440382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__21_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__22_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9157335234495081833 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__23_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__24_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4094575179031643265 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__25_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3178625304776205340 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0: f64 = 0.0;
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0: f64 = 0.0;
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1: f64 = 0.0;
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0: f64 = 0.0;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 99, 99, 101, 112, 116, 101, 100, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [46, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [67, 117, 114, 114, 101, 110, 116, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 115, 101, 116, 58, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [67, 111, 110, 115, 105, 100, 101, 114, 105, 110, 103, 32, 99, 97, 110, 100, 105, 100, 97, 116, 101, 115, 32, 119, 105, 116, 104, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_LibrarySuggestions_mepoSelector___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_LibrarySuggestions_mepoSelector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LibrarySuggestions_mepoSelector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_;
    v___x_2438_ = 0;
    v___x_2439_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__26_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_;
    v___x_2440_ = l_Lean_registerTraceClass(v___x_2437_, v___x_2438_, v___x_2439_);
    return v___x_2440_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2____boxed(
    mut v_a_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2442_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_();
    return v_res_2442_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(
    mut v_k_2443_: *mut crate::leanh::LeanObject,
    mut v_t_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2452_: u8 = 0;
    let mut v_impl_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2471_: u8 = 0;
    let mut v_size_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut v_unused_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_unused_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_unused_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v_size_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2560_: u8 = 0;
    let mut v_unused_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_k_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_unused_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_unused_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut v_unused_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v_unused_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_size_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: u8 = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2694_: u8 = 0;
    let mut v_unused_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_unused_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v_k_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_unused_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_unused_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_unused_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2782_: u8 = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v_size_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_unused_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v_unused_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut v_unused_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v_k_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2890_: u8 = 0;
    let mut v_unused_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2898_: u8 = 0;
    let mut v_k_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_unused_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_unused_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_unused_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2956_: u8 = 0;
    let mut v_size_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v_unused_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v_size_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_unused_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_unused_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v_k_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3087_: u8 = 0;
    let mut v_unused_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut v_unused_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_unused_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2444_) == 0 {
                    v_k_2445_ = crate::leanh::lean_ctor_get(v_t_2444_, 1);
                    v_v_2446_ = crate::leanh::lean_ctor_get(v_t_2444_, 2);
                    v_l_2447_ = crate::leanh::lean_ctor_get(v_t_2444_, 3);
                    v_r_2448_ = crate::leanh::lean_ctor_get(v_t_2444_, 4);
                    v_isSharedCheck_3102_ = (!crate::leanh::lean_is_exclusive(v_t_2444_)) as u8;
                    if v_isSharedCheck_3102_ == 0 {
                        v_unused_3103_ = crate::leanh::lean_ctor_get(v_t_2444_, 0);
                        crate::leanh::lean_dec(v_unused_3103_);
                        v___x_2450_ = v_t_2444_;
                        v_isShared_2451_ = v_isSharedCheck_3102_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2448_);
                        crate::leanh::lean_inc(v_l_2447_);
                        crate::leanh::lean_inc(v_v_2446_);
                        crate::leanh::lean_inc(v_k_2445_);
                        crate::leanh::lean_dec(v_t_2444_);
                        v___x_2450_ = crate::leanh::lean_box(0);
                        v_isShared_2451_ = v_isSharedCheck_3102_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_2444_;
                }
            }
            1 => {
                v___x_2452_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2443_, v_k_2445_);
                match v___x_2452_ {
                    0 => {
                        v_impl_2453_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_2443_, v_l_2447_);
                        v___x_2454_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_2453_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_2448_) == 0 {
                                v_size_2455_ = crate::leanh::lean_ctor_get(v_impl_2453_, 0);
                                crate::leanh::lean_inc(v_size_2455_);
                                v_size_2456_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                v_k_2457_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                v_v_2458_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                v_l_2459_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                crate::leanh::lean_inc(v_l_2459_);
                                v_r_2460_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                v___x_2461_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2462_ = lean_nat_mul(v___x_2461_, v_size_2455_);
                                v___x_2463_ = lean_nat_dec_lt(v___x_2462_, v_size_2456_);
                                crate::leanh::lean_dec(v___x_2462_);
                                if v___x_2463_ == 0 {
                                    crate::leanh::lean_dec(v_l_2459_);
                                    v___x_2464_ = lean_nat_add(v___x_2454_, v_size_2455_);
                                    crate::leanh::lean_dec(v_size_2455_);
                                    v___x_2465_ = lean_nat_add(v___x_2464_, v_size_2456_);
                                    crate::leanh::lean_dec(v___x_2464_);
                                    if v_isShared_2451_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2450_, 3, v_impl_2453_);
                                        crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2465_);
                                        v___x_2467_ = v___x_2450_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2468_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2468_,
                                            0,
                                            v___x_2465_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2468_,
                                            1,
                                            v_k_2445_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2468_,
                                            2,
                                            v_v_2446_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2468_,
                                            3,
                                            v_impl_2453_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2468_,
                                            4,
                                            v_r_2448_,
                                        );
                                        v___x_2467_ = v_reuseFailAlloc_2468_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_2460_);
                                    crate::leanh::lean_inc(v_v_2458_);
                                    crate::leanh::lean_inc(v_k_2457_);
                                    crate::leanh::lean_inc(v_size_2456_);
                                    v_isSharedCheck_2532_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                    if v_isSharedCheck_2532_ == 0 {
                                        v_unused_2533_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                        crate::leanh::lean_dec(v_unused_2533_);
                                        v_unused_2534_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                        crate::leanh::lean_dec(v_unused_2534_);
                                        v_unused_2535_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        crate::leanh::lean_dec(v_unused_2535_);
                                        v_unused_2536_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        crate::leanh::lean_dec(v_unused_2536_);
                                        v_unused_2537_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                        crate::leanh::lean_dec(v_unused_2537_);
                                        v___x_2470_ = v_r_2448_;
                                        v_isShared_2471_ = v_isSharedCheck_2532_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_2448_);
                                        v___x_2470_ = crate::leanh::lean_box(0);
                                        v_isShared_2471_ = v_isSharedCheck_2532_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2538_ = crate::leanh::lean_ctor_get(v_impl_2453_, 0);
                                crate::leanh::lean_inc(v_size_2538_);
                                v___x_2539_ = lean_nat_add(v___x_2454_, v_size_2538_);
                                crate::leanh::lean_dec(v_size_2538_);
                                if v_isShared_2451_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_impl_2453_);
                                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2539_);
                                    v___x_2541_ = v___x_2450_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2542_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2542_,
                                        0,
                                        v___x_2539_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2542_,
                                        1,
                                        v_k_2445_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2542_,
                                        2,
                                        v_v_2446_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2542_,
                                        3,
                                        v_impl_2453_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2542_,
                                        4,
                                        v_r_2448_,
                                    );
                                    v___x_2541_ = v_reuseFailAlloc_2542_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_r_2448_) == 0 {
                                v_l_2543_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                crate::leanh::lean_inc(v_l_2543_);
                                if crate::leanh::lean_obj_tag(v_l_2543_) == 0 {
                                    v_r_2544_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                    crate::leanh::lean_inc(v_r_2544_);
                                    if crate::leanh::lean_obj_tag(v_r_2544_) == 0 {
                                        v_size_2545_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                        v_k_2546_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        v_v_2547_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        v_isSharedCheck_2560_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                        if v_isSharedCheck_2560_ == 0 {
                                            v_unused_2561_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                            crate::leanh::lean_dec(v_unused_2561_);
                                            v_unused_2562_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                            crate::leanh::lean_dec(v_unused_2562_);
                                            v___x_2549_ = v_r_2448_;
                                            v_isShared_2550_ = v_isSharedCheck_2560_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2547_);
                                            crate::leanh::lean_inc(v_k_2546_);
                                            crate::leanh::lean_inc(v_size_2545_);
                                            crate::leanh::lean_dec(v_r_2448_);
                                            v___x_2549_ = crate::leanh::lean_box(0);
                                            v_isShared_2550_ = v_isSharedCheck_2560_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_2563_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        v_v_2564_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        v_isSharedCheck_2587_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                        if v_isSharedCheck_2587_ == 0 {
                                            v_unused_2588_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                            crate::leanh::lean_dec(v_unused_2588_);
                                            v_unused_2589_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                            crate::leanh::lean_dec(v_unused_2589_);
                                            v_unused_2590_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                            crate::leanh::lean_dec(v_unused_2590_);
                                            v___x_2566_ = v_r_2448_;
                                            v_isShared_2567_ = v_isSharedCheck_2587_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2564_);
                                            crate::leanh::lean_inc(v_k_2563_);
                                            crate::leanh::lean_dec(v_r_2448_);
                                            v___x_2566_ = crate::leanh::lean_box(0);
                                            v_isShared_2567_ = v_isSharedCheck_2587_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2591_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                    crate::leanh::lean_inc(v_r_2591_);
                                    if crate::leanh::lean_obj_tag(v_r_2591_) == 0 {
                                        v_k_2592_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        v_v_2593_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        v_isSharedCheck_2604_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                        if v_isSharedCheck_2604_ == 0 {
                                            v_unused_2605_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                            crate::leanh::lean_dec(v_unused_2605_);
                                            v_unused_2606_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                            crate::leanh::lean_dec(v_unused_2606_);
                                            v_unused_2607_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                            crate::leanh::lean_dec(v_unused_2607_);
                                            v___x_2595_ = v_r_2448_;
                                            v_isShared_2596_ = v_isSharedCheck_2604_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2593_);
                                            crate::leanh::lean_inc(v_k_2592_);
                                            crate::leanh::lean_dec(v_r_2448_);
                                            v___x_2595_ = crate::leanh::lean_box(0);
                                            v_isShared_2596_ = v_isSharedCheck_2604_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_2608_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                        v_k_2609_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        v_v_2610_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        v_isSharedCheck_2621_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                        if v_isSharedCheck_2621_ == 0 {
                                            v_unused_2622_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                            crate::leanh::lean_dec(v_unused_2622_);
                                            v_unused_2623_ =
                                                crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                            crate::leanh::lean_dec(v_unused_2623_);
                                            v___x_2612_ = v_r_2448_;
                                            v_isShared_2613_ = v_isSharedCheck_2621_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2610_);
                                            crate::leanh::lean_inc(v_k_2609_);
                                            crate::leanh::lean_inc(v_size_2608_);
                                            crate::leanh::lean_dec(v_r_2448_);
                                            v___x_2612_ = crate::leanh::lean_box(0);
                                            v_isShared_2613_ = v_isSharedCheck_2621_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2451_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_r_2448_);
                                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2454_);
                                    v___x_2625_ = v___x_2450_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2626_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2626_,
                                        0,
                                        v___x_2454_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2626_,
                                        1,
                                        v_k_2445_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2626_,
                                        2,
                                        v_v_2446_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2626_,
                                        3,
                                        v_r_2448_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2626_,
                                        4,
                                        v_r_2448_,
                                    );
                                    v___x_2625_ = v_reuseFailAlloc_2626_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_2450_);
                        crate::leanh::lean_dec(v_v_2446_);
                        crate::leanh::lean_dec(v_k_2445_);
                        if crate::leanh::lean_obj_tag(v_l_2447_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_2448_) == 0 {
                                v_size_2627_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                v_k_2628_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                v_v_2629_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                v_l_2630_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                v_r_2631_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                crate::leanh::lean_inc(v_r_2631_);
                                v_size_2632_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                v_k_2633_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                v_v_2634_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                v_l_2635_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                crate::leanh::lean_inc(v_l_2635_);
                                v_r_2636_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                v___x_2637_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2638_ = lean_nat_dec_lt(v_size_2627_, v_size_2632_);
                                if v___x_2638_ == 0 {
                                    crate::leanh::lean_inc(v_l_2630_);
                                    crate::leanh::lean_inc(v_v_2629_);
                                    crate::leanh::lean_inc(v_k_2628_);
                                    v_isSharedCheck_2774_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                                    if v_isSharedCheck_2774_ == 0 {
                                        v_unused_2775_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                        crate::leanh::lean_dec(v_unused_2775_);
                                        v_unused_2776_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                        crate::leanh::lean_dec(v_unused_2776_);
                                        v_unused_2777_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                        crate::leanh::lean_dec(v_unused_2777_);
                                        v_unused_2778_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                        crate::leanh::lean_dec(v_unused_2778_);
                                        v_unused_2779_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                        crate::leanh::lean_dec(v_unused_2779_);
                                        v___x_2640_ = v_l_2447_;
                                        v_isShared_2641_ = v_isSharedCheck_2774_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_2447_);
                                        v___x_2640_ = crate::leanh::lean_box(0);
                                        v_isShared_2641_ = v_isSharedCheck_2774_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_2636_);
                                    crate::leanh::lean_inc(v_v_2634_);
                                    crate::leanh::lean_inc(v_k_2633_);
                                    v_isSharedCheck_2932_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                                    if v_isSharedCheck_2932_ == 0 {
                                        v_unused_2933_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                                        crate::leanh::lean_dec(v_unused_2933_);
                                        v_unused_2934_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                                        crate::leanh::lean_dec(v_unused_2934_);
                                        v_unused_2935_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                                        crate::leanh::lean_dec(v_unused_2935_);
                                        v_unused_2936_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                                        crate::leanh::lean_dec(v_unused_2936_);
                                        v_unused_2937_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                                        crate::leanh::lean_dec(v_unused_2937_);
                                        v___x_2781_ = v_r_2448_;
                                        v_isShared_2782_ = v_isSharedCheck_2932_;
                                        state = 51;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_2448_);
                                        v___x_2781_ = crate::leanh::lean_box(0);
                                        v_isShared_2782_ = v_isSharedCheck_2932_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_2447_;
                            }
                        } else {
                            return v_r_2448_;
                        }
                    }
                    _ => {
                        v_impl_2938_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_2443_, v_r_2448_);
                        v___x_2939_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_2938_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_2447_) == 0 {
                                v_size_2940_ = crate::leanh::lean_ctor_get(v_impl_2938_, 0);
                                crate::leanh::lean_inc(v_size_2940_);
                                v_size_2941_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                v_k_2942_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                v_v_2943_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                v_l_2944_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                v_r_2945_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                crate::leanh::lean_inc(v_r_2945_);
                                v___x_2946_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2947_ = lean_nat_mul(v___x_2946_, v_size_2940_);
                                v___x_2948_ = lean_nat_dec_lt(v___x_2947_, v_size_2941_);
                                crate::leanh::lean_dec(v___x_2947_);
                                if v___x_2948_ == 0 {
                                    crate::leanh::lean_dec(v_r_2945_);
                                    v___x_2949_ = lean_nat_add(v___x_2939_, v_size_2941_);
                                    v___x_2950_ = lean_nat_add(v___x_2949_, v_size_2940_);
                                    crate::leanh::lean_dec(v_size_2940_);
                                    crate::leanh::lean_dec(v___x_2949_);
                                    if v_isShared_2451_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2450_, 4, v_impl_2938_);
                                        crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2950_);
                                        v___x_2952_ = v___x_2450_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2953_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2953_,
                                            0,
                                            v___x_2950_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2953_,
                                            1,
                                            v_k_2445_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2953_,
                                            2,
                                            v_v_2446_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2953_,
                                            3,
                                            v_l_2447_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2953_,
                                            4,
                                            v_impl_2938_,
                                        );
                                        v___x_2952_ = v_reuseFailAlloc_2953_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_2944_);
                                    crate::leanh::lean_inc(v_v_2943_);
                                    crate::leanh::lean_inc(v_k_2942_);
                                    crate::leanh::lean_inc(v_size_2941_);
                                    v_isSharedCheck_3019_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                                    if v_isSharedCheck_3019_ == 0 {
                                        v_unused_3020_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                        crate::leanh::lean_dec(v_unused_3020_);
                                        v_unused_3021_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                        crate::leanh::lean_dec(v_unused_3021_);
                                        v_unused_3022_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                        crate::leanh::lean_dec(v_unused_3022_);
                                        v_unused_3023_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                        crate::leanh::lean_dec(v_unused_3023_);
                                        v_unused_3024_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                        crate::leanh::lean_dec(v_unused_3024_);
                                        v___x_2955_ = v_l_2447_;
                                        v_isShared_2956_ = v_isSharedCheck_3019_;
                                        state = 75;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_2447_);
                                        v___x_2955_ = crate::leanh::lean_box(0);
                                        v_isShared_2956_ = v_isSharedCheck_3019_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3025_ = crate::leanh::lean_ctor_get(v_impl_2938_, 0);
                                crate::leanh::lean_inc(v_size_3025_);
                                v___x_3026_ = lean_nat_add(v___x_2939_, v_size_3025_);
                                crate::leanh::lean_dec(v_size_3025_);
                                if v_isShared_2451_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_impl_2938_);
                                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_3026_);
                                    v___x_3028_ = v___x_2450_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3029_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3029_,
                                        0,
                                        v___x_3026_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3029_,
                                        1,
                                        v_k_2445_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3029_,
                                        2,
                                        v_v_2446_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3029_,
                                        3,
                                        v_l_2447_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3029_,
                                        4,
                                        v_impl_2938_,
                                    );
                                    v___x_3028_ = v_reuseFailAlloc_3029_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_2447_) == 0 {
                                v_l_3030_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                if crate::leanh::lean_obj_tag(v_l_3030_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_3030_);
                                    v_r_3031_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                    crate::leanh::lean_inc(v_r_3031_);
                                    if crate::leanh::lean_obj_tag(v_r_3031_) == 0 {
                                        v_size_3032_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                        v_k_3033_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                        v_v_3034_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                        v_isSharedCheck_3047_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                                        if v_isSharedCheck_3047_ == 0 {
                                            v_unused_3048_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                            crate::leanh::lean_dec(v_unused_3048_);
                                            v_unused_3049_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                            crate::leanh::lean_dec(v_unused_3049_);
                                            v___x_3036_ = v_l_2447_;
                                            v_isShared_3037_ = v_isSharedCheck_3047_;
                                            state = 86;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3034_);
                                            crate::leanh::lean_inc(v_k_3033_);
                                            crate::leanh::lean_inc(v_size_3032_);
                                            crate::leanh::lean_dec(v_l_2447_);
                                            v___x_3036_ = crate::leanh::lean_box(0);
                                            v_isShared_3037_ = v_isSharedCheck_3047_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_3050_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                        v_v_3051_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                        v_isSharedCheck_3062_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                                        if v_isSharedCheck_3062_ == 0 {
                                            v_unused_3063_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                            crate::leanh::lean_dec(v_unused_3063_);
                                            v_unused_3064_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                            crate::leanh::lean_dec(v_unused_3064_);
                                            v_unused_3065_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                            crate::leanh::lean_dec(v_unused_3065_);
                                            v___x_3053_ = v_l_2447_;
                                            v_isShared_3054_ = v_isSharedCheck_3062_;
                                            state = 89;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3051_);
                                            crate::leanh::lean_inc(v_k_3050_);
                                            crate::leanh::lean_dec(v_l_2447_);
                                            v___x_3053_ = crate::leanh::lean_box(0);
                                            v_isShared_3054_ = v_isSharedCheck_3062_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3066_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                    crate::leanh::lean_inc(v_r_3066_);
                                    if crate::leanh::lean_obj_tag(v_r_3066_) == 0 {
                                        crate::leanh::lean_inc(v_l_3030_);
                                        v_k_3067_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                        v_v_3068_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                        v_isSharedCheck_3091_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                                        if v_isSharedCheck_3091_ == 0 {
                                            v_unused_3092_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                            crate::leanh::lean_dec(v_unused_3092_);
                                            v_unused_3093_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                            crate::leanh::lean_dec(v_unused_3093_);
                                            v_unused_3094_ =
                                                crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                            crate::leanh::lean_dec(v_unused_3094_);
                                            v___x_3070_ = v_l_2447_;
                                            v_isShared_3071_ = v_isSharedCheck_3091_;
                                            state = 92;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3068_);
                                            crate::leanh::lean_inc(v_k_3067_);
                                            crate::leanh::lean_dec(v_l_2447_);
                                            v___x_3070_ = crate::leanh::lean_box(0);
                                            v_isShared_3071_ = v_isSharedCheck_3091_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_3095_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_2451_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_2450_, 4, v_r_3066_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2450_,
                                                0,
                                                v___x_3095_,
                                            );
                                            v___x_3097_ = v___x_2450_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3098_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3098_,
                                                0,
                                                v___x_3095_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3098_,
                                                1,
                                                v_k_2445_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3098_,
                                                2,
                                                v_v_2446_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3098_,
                                                3,
                                                v_l_2447_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3098_,
                                                4,
                                                v_r_3066_,
                                            );
                                            v___x_3097_ = v_reuseFailAlloc_3098_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_2451_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_l_2447_);
                                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2939_);
                                    v___x_3100_ = v___x_2450_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3101_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3101_,
                                        0,
                                        v___x_2939_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3101_,
                                        1,
                                        v_k_2445_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3101_,
                                        2,
                                        v_v_2446_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3101_,
                                        3,
                                        v_l_2447_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3101_,
                                        4,
                                        v_l_2447_,
                                    );
                                    v___x_3100_ = v_reuseFailAlloc_3101_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2467_;
            }
            3 => {
                v_size_2472_ = crate::leanh::lean_ctor_get(v_l_2459_, 0);
                v_k_2473_ = crate::leanh::lean_ctor_get(v_l_2459_, 1);
                v_v_2474_ = crate::leanh::lean_ctor_get(v_l_2459_, 2);
                v_l_2475_ = crate::leanh::lean_ctor_get(v_l_2459_, 3);
                v_r_2476_ = crate::leanh::lean_ctor_get(v_l_2459_, 4);
                v_size_2477_ = crate::leanh::lean_ctor_get(v_r_2460_, 0);
                v___x_2478_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2479_ = lean_nat_mul(v___x_2478_, v_size_2477_);
                v___x_2480_ = lean_nat_dec_lt(v_size_2472_, v___x_2479_);
                crate::leanh::lean_dec(v___x_2479_);
                if v___x_2480_ == 0 {
                    crate::leanh::lean_inc(v_r_2476_);
                    crate::leanh::lean_inc(v_l_2475_);
                    crate::leanh::lean_inc(v_v_2474_);
                    crate::leanh::lean_inc(v_k_2473_);
                    v_isSharedCheck_2508_ = (!crate::leanh::lean_is_exclusive(v_l_2459_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v_unused_2509_ = crate::leanh::lean_ctor_get(v_l_2459_, 4);
                        crate::leanh::lean_dec(v_unused_2509_);
                        v_unused_2510_ = crate::leanh::lean_ctor_get(v_l_2459_, 3);
                        crate::leanh::lean_dec(v_unused_2510_);
                        v_unused_2511_ = crate::leanh::lean_ctor_get(v_l_2459_, 2);
                        crate::leanh::lean_dec(v_unused_2511_);
                        v_unused_2512_ = crate::leanh::lean_ctor_get(v_l_2459_, 1);
                        crate::leanh::lean_dec(v_unused_2512_);
                        v_unused_2513_ = crate::leanh::lean_ctor_get(v_l_2459_, 0);
                        crate::leanh::lean_dec(v_unused_2513_);
                        v___x_2482_ = v_l_2459_;
                        v_isShared_2483_ = v_isSharedCheck_2508_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2459_);
                        v___x_2482_ = crate::leanh::lean_box(0);
                        v_isShared_2483_ = v_isSharedCheck_2508_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2450_);
                    v___x_2514_ = lean_nat_add(v___x_2454_, v_size_2455_);
                    crate::leanh::lean_dec(v_size_2455_);
                    v___x_2515_ = lean_nat_add(v___x_2514_, v_size_2456_);
                    crate::leanh::lean_dec(v_size_2456_);
                    v___x_2516_ = lean_nat_add(v___x_2514_, v_size_2472_);
                    crate::leanh::lean_dec(v___x_2514_);
                    crate::leanh::lean_inc_ref(v_impl_2453_);
                    if v_isShared_2471_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2470_, 4, v_l_2459_);
                        crate::leanh::lean_ctor_set(v___x_2470_, 3, v_impl_2453_);
                        crate::leanh::lean_ctor_set(v___x_2470_, 2, v_v_2446_);
                        crate::leanh::lean_ctor_set(v___x_2470_, 1, v_k_2445_);
                        crate::leanh::lean_ctor_set(v___x_2470_, 0, v___x_2516_);
                        v___x_2518_ = v___x_2470_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2531_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2516_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2445_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2446_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_impl_2453_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_l_2459_);
                        v___x_2518_ = v_reuseFailAlloc_2531_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2484_ = lean_nat_add(v___x_2454_, v_size_2455_);
                crate::leanh::lean_dec(v_size_2455_);
                v___x_2485_ = lean_nat_add(v___x_2484_, v_size_2456_);
                crate::leanh::lean_dec(v_size_2456_);
                if crate::leanh::lean_obj_tag(v_l_2475_) == 0 {
                    v_size_2506_ = crate::leanh::lean_ctor_get(v_l_2475_, 0);
                    crate::leanh::lean_inc(v_size_2506_);
                    v___y_2498_ = v_size_2506_;
                    state = 8;
                    continue;
                } else {
                    v___x_2507_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2498_ = v___x_2507_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2490_ = lean_nat_add(v___y_2488_, v___y_2489_);
                crate::leanh::lean_dec(v___y_2489_);
                crate::leanh::lean_dec(v___y_2488_);
                if v_isShared_2483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2482_, 4, v_r_2460_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 3, v_r_2476_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 2, v_v_2458_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 1, v_k_2457_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2490_);
                    v___x_2492_ = v___x_2482_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2496_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_k_2457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_v_2458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_r_2476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_r_2460_);
                    v___x_2492_ = v_reuseFailAlloc_2496_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2470_, 4, v___x_2492_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 3, v___y_2487_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 2, v_v_2474_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 1, v_k_2473_);
                    crate::leanh::lean_ctor_set(v___x_2470_, 0, v___x_2485_);
                    v___x_2494_ = v___x_2470_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 1, v_k_2473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_v_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 3, v___y_2487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 4, v___x_2492_);
                    v___x_2494_ = v_reuseFailAlloc_2495_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2494_;
            }
            8 => {
                v___x_2499_ = lean_nat_add(v___x_2484_, v___y_2498_);
                crate::leanh::lean_dec(v___y_2498_);
                crate::leanh::lean_dec(v___x_2484_);
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_l_2475_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_impl_2453_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2499_);
                    v___x_2501_ = v___x_2450_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_impl_2453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_l_2475_);
                    v___x_2501_ = v_reuseFailAlloc_2505_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2502_ = lean_nat_add(v___x_2454_, v_size_2477_);
                if crate::leanh::lean_obj_tag(v_r_2476_) == 0 {
                    v_size_2503_ = crate::leanh::lean_ctor_get(v_r_2476_, 0);
                    crate::leanh::lean_inc(v_size_2503_);
                    v___y_2487_ = v___x_2501_;
                    v___y_2488_ = v___x_2502_;
                    v___y_2489_ = v_size_2503_;
                    state = 5;
                    continue;
                } else {
                    v___x_2504_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2487_ = v___x_2501_;
                    v___y_2488_ = v___x_2502_;
                    v___y_2489_ = v___x_2504_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2525_ = (!crate::leanh::lean_is_exclusive(v_impl_2453_)) as u8;
                if v_isSharedCheck_2525_ == 0 {
                    v_unused_2526_ = crate::leanh::lean_ctor_get(v_impl_2453_, 4);
                    crate::leanh::lean_dec(v_unused_2526_);
                    v_unused_2527_ = crate::leanh::lean_ctor_get(v_impl_2453_, 3);
                    crate::leanh::lean_dec(v_unused_2527_);
                    v_unused_2528_ = crate::leanh::lean_ctor_get(v_impl_2453_, 2);
                    crate::leanh::lean_dec(v_unused_2528_);
                    v_unused_2529_ = crate::leanh::lean_ctor_get(v_impl_2453_, 1);
                    crate::leanh::lean_dec(v_unused_2529_);
                    v_unused_2530_ = crate::leanh::lean_ctor_get(v_impl_2453_, 0);
                    crate::leanh::lean_dec(v_unused_2530_);
                    v___x_2520_ = v_impl_2453_;
                    v_isShared_2521_ = v_isSharedCheck_2525_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_2453_);
                    v___x_2520_ = crate::leanh::lean_box(0);
                    v_isShared_2521_ = v_isSharedCheck_2525_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2520_, 4, v_r_2460_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 3, v___x_2518_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 2, v_v_2458_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 1, v_k_2457_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2515_);
                    v___x_2523_ = v___x_2520_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_k_2457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_v_2458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 3, v___x_2518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_r_2460_);
                    v___x_2523_ = v_reuseFailAlloc_2524_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2523_;
            }
            13 => {
                return v___x_2541_;
            }
            14 => {
                v_size_2551_ = crate::leanh::lean_ctor_get(v_l_2543_, 0);
                v___x_2552_ = lean_nat_add(v___x_2454_, v_size_2545_);
                crate::leanh::lean_dec(v_size_2545_);
                v___x_2553_ = lean_nat_add(v___x_2454_, v_size_2551_);
                if v_isShared_2550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2549_, 4, v_l_2543_);
                    crate::leanh::lean_ctor_set(v___x_2549_, 3, v_impl_2453_);
                    crate::leanh::lean_ctor_set(v___x_2549_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_2549_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_2549_, 0, v___x_2553_);
                    v___x_2555_ = v___x_2549_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 3, v_impl_2453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 4, v_l_2543_);
                    v___x_2555_ = v_reuseFailAlloc_2559_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_r_2544_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v___x_2555_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_2547_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_2546_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2552_);
                    v___x_2557_ = v___x_2450_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_k_2546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_v_2547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 3, v___x_2555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_r_2544_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2557_;
            }
            17 => {
                v_k_2568_ = crate::leanh::lean_ctor_get(v_l_2543_, 1);
                v_v_2569_ = crate::leanh::lean_ctor_get(v_l_2543_, 2);
                v_isSharedCheck_2583_ = (!crate::leanh::lean_is_exclusive(v_l_2543_)) as u8;
                if v_isSharedCheck_2583_ == 0 {
                    v_unused_2584_ = crate::leanh::lean_ctor_get(v_l_2543_, 4);
                    crate::leanh::lean_dec(v_unused_2584_);
                    v_unused_2585_ = crate::leanh::lean_ctor_get(v_l_2543_, 3);
                    crate::leanh::lean_dec(v_unused_2585_);
                    v_unused_2586_ = crate::leanh::lean_ctor_get(v_l_2543_, 0);
                    crate::leanh::lean_dec(v_unused_2586_);
                    v___x_2571_ = v_l_2543_;
                    v_isShared_2572_ = v_isSharedCheck_2583_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2569_);
                    crate::leanh::lean_inc(v_k_2568_);
                    crate::leanh::lean_dec(v_l_2543_);
                    v___x_2571_ = crate::leanh::lean_box(0);
                    v_isShared_2572_ = v_isSharedCheck_2583_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2573_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2571_, 4, v_r_2544_);
                    crate::leanh::lean_ctor_set(v___x_2571_, 3, v_r_2544_);
                    crate::leanh::lean_ctor_set(v___x_2571_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_2571_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_2571_, 0, v___x_2454_);
                    v___x_2575_ = v___x_2571_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 3, v_r_2544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 4, v_r_2544_);
                    v___x_2575_ = v_reuseFailAlloc_2582_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2566_, 3, v_r_2544_);
                    crate::leanh::lean_ctor_set(v___x_2566_, 0, v___x_2454_);
                    v___x_2577_ = v___x_2566_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_r_2544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_r_2544_);
                    v___x_2577_ = v_reuseFailAlloc_2581_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v___x_2577_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v___x_2575_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_2569_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_2568_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2573_);
                    v___x_2579_ = v___x_2450_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_k_2568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_v_2569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 3, v___x_2575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 4, v___x_2577_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2579_;
            }
            22 => {
                v___x_2597_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2595_, 4, v_l_2543_);
                    crate::leanh::lean_ctor_set(v___x_2595_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_2595_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_2595_, 0, v___x_2454_);
                    v___x_2599_ = v___x_2595_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_l_2543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_l_2543_);
                    v___x_2599_ = v_reuseFailAlloc_2603_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_r_2591_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v___x_2599_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_2593_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_2592_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2597_);
                    v___x_2601_ = v___x_2450_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_k_2592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 2, v_v_2593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 3, v___x_2599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 4, v_r_2591_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2601_;
            }
            25 => {
                if v_isShared_2613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2612_, 3, v_r_2591_);
                    v___x_2615_ = v___x_2612_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2620_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_size_2608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_k_2609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_v_2610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_r_2591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 4, v_r_2591_);
                    v___x_2615_ = v_reuseFailAlloc_2620_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2616_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v___x_2615_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_r_2591_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2616_);
                    v___x_2618_ = v___x_2450_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2619_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_r_2591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2619_, 4, v___x_2615_);
                    v___x_2618_ = v_reuseFailAlloc_2619_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2618_;
            }
            28 => {
                return v___x_2625_;
            }
            29 => {
                v___x_2642_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_2628_, v_v_2629_, v_l_2630_, v_r_2631_,
                );
                v_tree_2643_ = crate::leanh::lean_ctor_get(v___x_2642_, 2);
                crate::leanh::lean_inc(v_tree_2643_);
                if crate::leanh::lean_obj_tag(v_tree_2643_) == 0 {
                    v_k_2644_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                    crate::leanh::lean_inc(v_k_2644_);
                    v_v_2645_ = crate::leanh::lean_ctor_get(v___x_2642_, 1);
                    crate::leanh::lean_inc(v_v_2645_);
                    crate::leanh::lean_dec_ref(v___x_2642_);
                    v_size_2646_ = crate::leanh::lean_ctor_get(v_tree_2643_, 0);
                    v___x_2647_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2648_ = lean_nat_mul(v___x_2647_, v_size_2646_);
                    v___x_2649_ = lean_nat_dec_lt(v___x_2648_, v_size_2632_);
                    crate::leanh::lean_dec(v___x_2648_);
                    if v___x_2649_ == 0 {
                        crate::leanh::lean_dec(v_l_2635_);
                        v___x_2650_ = lean_nat_add(v___x_2637_, v_size_2646_);
                        v___x_2651_ = lean_nat_add(v___x_2650_, v_size_2632_);
                        crate::leanh::lean_dec(v___x_2650_);
                        if v_isShared_2641_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2640_, 4, v_r_2448_);
                            crate::leanh::lean_ctor_set(v___x_2640_, 3, v_tree_2643_);
                            crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2645_);
                            crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2644_);
                            crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2651_);
                            v___x_2653_ = v___x_2640_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_2654_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_k_2644_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_v_2645_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 3, v_tree_2643_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 4, v_r_2448_);
                            v___x_2653_ = v_reuseFailAlloc_2654_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_2636_);
                        crate::leanh::lean_inc(v_v_2634_);
                        crate::leanh::lean_inc(v_k_2633_);
                        crate::leanh::lean_inc(v_size_2632_);
                        v_isSharedCheck_2709_ = (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                        if v_isSharedCheck_2709_ == 0 {
                            v_unused_2710_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                            crate::leanh::lean_dec(v_unused_2710_);
                            v_unused_2711_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                            crate::leanh::lean_dec(v_unused_2711_);
                            v_unused_2712_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                            crate::leanh::lean_dec(v_unused_2712_);
                            v_unused_2713_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                            crate::leanh::lean_dec(v_unused_2713_);
                            v_unused_2714_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                            crate::leanh::lean_dec(v_unused_2714_);
                            v___x_2656_ = v_r_2448_;
                            v_isShared_2657_ = v_isSharedCheck_2709_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_2448_);
                            v___x_2656_ = crate::leanh::lean_box(0);
                            v_isShared_2657_ = v_isSharedCheck_2709_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_2636_);
                    crate::leanh::lean_inc(v_v_2634_);
                    crate::leanh::lean_inc(v_k_2633_);
                    crate::leanh::lean_inc(v_size_2632_);
                    v_isSharedCheck_2768_ = (!crate::leanh::lean_is_exclusive(v_r_2448_)) as u8;
                    if v_isSharedCheck_2768_ == 0 {
                        v_unused_2769_ = crate::leanh::lean_ctor_get(v_r_2448_, 4);
                        crate::leanh::lean_dec(v_unused_2769_);
                        v_unused_2770_ = crate::leanh::lean_ctor_get(v_r_2448_, 3);
                        crate::leanh::lean_dec(v_unused_2770_);
                        v_unused_2771_ = crate::leanh::lean_ctor_get(v_r_2448_, 2);
                        crate::leanh::lean_dec(v_unused_2771_);
                        v_unused_2772_ = crate::leanh::lean_ctor_get(v_r_2448_, 1);
                        crate::leanh::lean_dec(v_unused_2772_);
                        v_unused_2773_ = crate::leanh::lean_ctor_get(v_r_2448_, 0);
                        crate::leanh::lean_dec(v_unused_2773_);
                        v___x_2716_ = v_r_2448_;
                        v_isShared_2717_ = v_isSharedCheck_2768_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2448_);
                        v___x_2716_ = crate::leanh::lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2768_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_2653_;
            }
            31 => {
                v_size_2658_ = crate::leanh::lean_ctor_get(v_l_2635_, 0);
                v_k_2659_ = crate::leanh::lean_ctor_get(v_l_2635_, 1);
                v_v_2660_ = crate::leanh::lean_ctor_get(v_l_2635_, 2);
                v_l_2661_ = crate::leanh::lean_ctor_get(v_l_2635_, 3);
                v_r_2662_ = crate::leanh::lean_ctor_get(v_l_2635_, 4);
                v_size_2663_ = crate::leanh::lean_ctor_get(v_r_2636_, 0);
                v___x_2664_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2665_ = lean_nat_mul(v___x_2664_, v_size_2663_);
                v___x_2666_ = lean_nat_dec_lt(v_size_2658_, v___x_2665_);
                crate::leanh::lean_dec(v___x_2665_);
                if v___x_2666_ == 0 {
                    crate::leanh::lean_inc(v_r_2662_);
                    crate::leanh::lean_inc(v_l_2661_);
                    crate::leanh::lean_inc(v_v_2660_);
                    crate::leanh::lean_inc(v_k_2659_);
                    v_isSharedCheck_2694_ = (!crate::leanh::lean_is_exclusive(v_l_2635_)) as u8;
                    if v_isSharedCheck_2694_ == 0 {
                        v_unused_2695_ = crate::leanh::lean_ctor_get(v_l_2635_, 4);
                        crate::leanh::lean_dec(v_unused_2695_);
                        v_unused_2696_ = crate::leanh::lean_ctor_get(v_l_2635_, 3);
                        crate::leanh::lean_dec(v_unused_2696_);
                        v_unused_2697_ = crate::leanh::lean_ctor_get(v_l_2635_, 2);
                        crate::leanh::lean_dec(v_unused_2697_);
                        v_unused_2698_ = crate::leanh::lean_ctor_get(v_l_2635_, 1);
                        crate::leanh::lean_dec(v_unused_2698_);
                        v_unused_2699_ = crate::leanh::lean_ctor_get(v_l_2635_, 0);
                        crate::leanh::lean_dec(v_unused_2699_);
                        v___x_2668_ = v_l_2635_;
                        v_isShared_2669_ = v_isSharedCheck_2694_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2635_);
                        v___x_2668_ = crate::leanh::lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2694_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_2700_ = lean_nat_add(v___x_2637_, v_size_2646_);
                    v___x_2701_ = lean_nat_add(v___x_2700_, v_size_2632_);
                    crate::leanh::lean_dec(v_size_2632_);
                    v___x_2702_ = lean_nat_add(v___x_2700_, v_size_2658_);
                    crate::leanh::lean_dec(v___x_2700_);
                    if v_isShared_2657_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2656_, 4, v_l_2635_);
                        crate::leanh::lean_ctor_set(v___x_2656_, 3, v_tree_2643_);
                        crate::leanh::lean_ctor_set(v___x_2656_, 2, v_v_2645_);
                        crate::leanh::lean_ctor_set(v___x_2656_, 1, v_k_2644_);
                        crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2702_);
                        v___x_2704_ = v___x_2656_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_2708_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_k_2644_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_v_2645_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 3, v_tree_2643_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 4, v_l_2635_);
                        v___x_2704_ = v_reuseFailAlloc_2708_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_2670_ = lean_nat_add(v___x_2637_, v_size_2646_);
                v___x_2671_ = lean_nat_add(v___x_2670_, v_size_2632_);
                crate::leanh::lean_dec(v_size_2632_);
                if crate::leanh::lean_obj_tag(v_l_2661_) == 0 {
                    v_size_2692_ = crate::leanh::lean_ctor_get(v_l_2661_, 0);
                    crate::leanh::lean_inc(v_size_2692_);
                    v___y_2684_ = v_size_2692_;
                    state = 36;
                    continue;
                } else {
                    v___x_2693_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2684_ = v___x_2693_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_2676_ = lean_nat_add(v___y_2674_, v___y_2675_);
                crate::leanh::lean_dec(v___y_2675_);
                crate::leanh::lean_dec(v___y_2674_);
                if v_isShared_2669_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2668_, 4, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2668_, 3, v_r_2662_);
                    crate::leanh::lean_ctor_set(v___x_2668_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v___x_2668_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v___x_2668_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2668_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 3, v_r_2662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 4, v_r_2636_);
                    v___x_2678_ = v_reuseFailAlloc_2682_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2656_, 4, v___x_2678_);
                    crate::leanh::lean_ctor_set(v___x_2656_, 3, v___y_2673_);
                    crate::leanh::lean_ctor_set(v___x_2656_, 2, v_v_2660_);
                    crate::leanh::lean_ctor_set(v___x_2656_, 1, v_k_2659_);
                    crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2671_);
                    v___x_2680_ = v___x_2656_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_k_2659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 2, v_v_2660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 3, v___y_2673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 4, v___x_2678_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2680_;
            }
            36 => {
                v___x_2685_ = lean_nat_add(v___x_2670_, v___y_2684_);
                crate::leanh::lean_dec(v___y_2684_);
                crate::leanh::lean_dec(v___x_2670_);
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v_l_2661_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v_tree_2643_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2645_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2644_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2685_);
                    v___x_2687_ = v___x_2640_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_k_2644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_v_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_tree_2643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 4, v_l_2661_);
                    v___x_2687_ = v_reuseFailAlloc_2691_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2688_ = lean_nat_add(v___x_2637_, v_size_2663_);
                if crate::leanh::lean_obj_tag(v_r_2662_) == 0 {
                    v_size_2689_ = crate::leanh::lean_ctor_get(v_r_2662_, 0);
                    crate::leanh::lean_inc(v_size_2689_);
                    v___y_2673_ = v___x_2687_;
                    v___y_2674_ = v___x_2688_;
                    v___y_2675_ = v_size_2689_;
                    state = 33;
                    continue;
                } else {
                    v___x_2690_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2673_ = v___x_2687_;
                    v___y_2674_ = v___x_2688_;
                    v___y_2675_ = v___x_2690_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v___x_2704_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2701_);
                    v___x_2706_ = v___x_2640_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 3, v___x_2704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 4, v_r_2636_);
                    v___x_2706_ = v_reuseFailAlloc_2707_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2706_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_l_2635_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2636_) == 0 {
                        v_k_2718_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                        crate::leanh::lean_inc(v_k_2718_);
                        v_v_2719_ = crate::leanh::lean_ctor_get(v___x_2642_, 1);
                        crate::leanh::lean_inc(v_v_2719_);
                        crate::leanh::lean_dec_ref(v___x_2642_);
                        v_size_2720_ = crate::leanh::lean_ctor_get(v_l_2635_, 0);
                        v___x_2721_ = lean_nat_add(v___x_2637_, v_size_2632_);
                        crate::leanh::lean_dec(v_size_2632_);
                        v___x_2722_ = lean_nat_add(v___x_2637_, v_size_2720_);
                        if v_isShared_2717_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2716_, 4, v_l_2635_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 3, v_tree_2643_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 2, v_v_2719_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 1, v_k_2718_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2722_);
                            v___x_2724_ = v___x_2716_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_2728_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2722_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_k_2718_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_v_2719_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_tree_2643_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_l_2635_);
                            v___x_2724_ = v_reuseFailAlloc_2728_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_2632_);
                        v_k_2729_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                        crate::leanh::lean_inc(v_k_2729_);
                        v_v_2730_ = crate::leanh::lean_ctor_get(v___x_2642_, 1);
                        crate::leanh::lean_inc(v_v_2730_);
                        crate::leanh::lean_dec_ref(v___x_2642_);
                        v_k_2731_ = crate::leanh::lean_ctor_get(v_l_2635_, 1);
                        v_v_2732_ = crate::leanh::lean_ctor_get(v_l_2635_, 2);
                        v_isSharedCheck_2746_ = (!crate::leanh::lean_is_exclusive(v_l_2635_)) as u8;
                        if v_isSharedCheck_2746_ == 0 {
                            v_unused_2747_ = crate::leanh::lean_ctor_get(v_l_2635_, 4);
                            crate::leanh::lean_dec(v_unused_2747_);
                            v_unused_2748_ = crate::leanh::lean_ctor_get(v_l_2635_, 3);
                            crate::leanh::lean_dec(v_unused_2748_);
                            v_unused_2749_ = crate::leanh::lean_ctor_get(v_l_2635_, 0);
                            crate::leanh::lean_dec(v_unused_2749_);
                            v___x_2734_ = v_l_2635_;
                            v_isShared_2735_ = v_isSharedCheck_2746_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_2732_);
                            crate::leanh::lean_inc(v_k_2731_);
                            crate::leanh::lean_dec(v_l_2635_);
                            v___x_2734_ = crate::leanh::lean_box(0);
                            v_isShared_2735_ = v_isSharedCheck_2746_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_2636_) == 0 {
                        crate::leanh::lean_dec(v_size_2632_);
                        v_k_2750_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                        crate::leanh::lean_inc(v_k_2750_);
                        v_v_2751_ = crate::leanh::lean_ctor_get(v___x_2642_, 1);
                        crate::leanh::lean_inc(v_v_2751_);
                        crate::leanh::lean_dec_ref(v___x_2642_);
                        v___x_2752_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_2717_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2716_, 4, v_l_2635_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 2, v_v_2751_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 1, v_k_2750_);
                            crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2637_);
                            v___x_2754_ = v___x_2716_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_2758_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2637_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_k_2750_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_v_2751_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_l_2635_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 4, v_l_2635_);
                            v___x_2754_ = v_reuseFailAlloc_2758_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_2759_ = crate::leanh::lean_ctor_get(v___x_2642_, 0);
                        crate::leanh::lean_inc(v_k_2759_);
                        v_v_2760_ = crate::leanh::lean_ctor_get(v___x_2642_, 1);
                        crate::leanh::lean_inc(v_v_2760_);
                        crate::leanh::lean_dec_ref(v___x_2642_);
                        if v_isShared_2717_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2716_, 3, v_r_2636_);
                            v___x_2762_ = v___x_2716_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_2767_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_size_2632_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_k_2633_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 2, v_v_2634_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 3, v_r_2636_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 4, v_r_2636_);
                            v___x_2762_ = v_reuseFailAlloc_2767_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v___x_2724_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2721_);
                    v___x_2726_ = v___x_2640_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 3, v___x_2724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 4, v_r_2636_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2726_;
            }
            43 => {
                v___x_2736_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2734_, 4, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2734_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2734_, 2, v_v_2730_);
                    crate::leanh::lean_ctor_set(v___x_2734_, 1, v_k_2729_);
                    crate::leanh::lean_ctor_set(v___x_2734_, 0, v___x_2637_);
                    v___x_2738_ = v___x_2734_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_k_2729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 2, v_v_2730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 4, v_r_2636_);
                    v___x_2738_ = v_reuseFailAlloc_2745_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_2717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2716_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2637_);
                    v___x_2740_ = v___x_2716_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 4, v_r_2636_);
                    v___x_2740_ = v_reuseFailAlloc_2744_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v___x_2740_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v___x_2738_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2732_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2731_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2736_);
                    v___x_2742_ = v___x_2640_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_k_2731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_v_2732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 3, v___x_2738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 4, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2743_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_2742_;
            }
            47 => {
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v___x_2754_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2752_);
                    v___x_2756_ = v___x_2640_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 1, v_k_2633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_v_2634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 3, v___x_2754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 4, v_r_2636_);
                    v___x_2756_ = v_reuseFailAlloc_2757_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_2756_;
            }
            49 => {
                v___x_2763_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_2641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2640_, 4, v___x_2762_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 2, v_v_2760_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_k_2759_);
                    crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2763_);
                    v___x_2765_ = v___x_2640_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 1, v_k_2759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_v_2760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_r_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 4, v___x_2762_);
                    v___x_2765_ = v_reuseFailAlloc_2766_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_2765_;
            }
            51 => {
                v___x_2783_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_2633_, v_v_2634_, v_l_2635_, v_r_2636_,
                );
                v_tree_2784_ = crate::leanh::lean_ctor_get(v___x_2783_, 2);
                crate::leanh::lean_inc(v_tree_2784_);
                if crate::leanh::lean_obj_tag(v_tree_2784_) == 0 {
                    v_k_2785_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    crate::leanh::lean_inc(v_k_2785_);
                    v_v_2786_ = crate::leanh::lean_ctor_get(v___x_2783_, 1);
                    crate::leanh::lean_inc(v_v_2786_);
                    crate::leanh::lean_dec_ref(v___x_2783_);
                    v_size_2787_ = crate::leanh::lean_ctor_get(v_tree_2784_, 0);
                    v___x_2788_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2789_ = lean_nat_mul(v___x_2788_, v_size_2787_);
                    v___x_2790_ = lean_nat_dec_lt(v___x_2789_, v_size_2627_);
                    crate::leanh::lean_dec(v___x_2789_);
                    if v___x_2790_ == 0 {
                        crate::leanh::lean_dec(v_r_2631_);
                        v___x_2791_ = lean_nat_add(v___x_2637_, v_size_2627_);
                        v___x_2792_ = lean_nat_add(v___x_2791_, v_size_2787_);
                        crate::leanh::lean_dec(v___x_2791_);
                        if v_isShared_2782_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2781_, 4, v_tree_2784_);
                            crate::leanh::lean_ctor_set(v___x_2781_, 3, v_l_2447_);
                            crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2786_);
                            crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2785_);
                            crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2792_);
                            v___x_2794_ = v___x_2781_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_2795_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_k_2785_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_v_2786_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 3, v_l_2447_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 4, v_tree_2784_);
                            v___x_2794_ = v_reuseFailAlloc_2795_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_2630_);
                        crate::leanh::lean_inc(v_v_2629_);
                        crate::leanh::lean_inc(v_k_2628_);
                        crate::leanh::lean_inc(v_size_2627_);
                        v_isSharedCheck_2861_ = (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v_unused_2862_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                            crate::leanh::lean_dec(v_unused_2862_);
                            v_unused_2863_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                            crate::leanh::lean_dec(v_unused_2863_);
                            v_unused_2864_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                            crate::leanh::lean_dec(v_unused_2864_);
                            v_unused_2865_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                            crate::leanh::lean_dec(v_unused_2865_);
                            v_unused_2866_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                            crate::leanh::lean_dec(v_unused_2866_);
                            v___x_2797_ = v_l_2447_;
                            v_isShared_2798_ = v_isSharedCheck_2861_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_2447_);
                            v___x_2797_ = crate::leanh::lean_box(0);
                            v_isShared_2798_ = v_isSharedCheck_2861_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_2630_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_2630_);
                        crate::leanh::lean_inc(v_v_2629_);
                        crate::leanh::lean_inc(v_k_2628_);
                        crate::leanh::lean_inc(v_size_2627_);
                        v_isSharedCheck_2890_ = (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                        if v_isSharedCheck_2890_ == 0 {
                            v_unused_2891_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                            crate::leanh::lean_dec(v_unused_2891_);
                            v_unused_2892_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                            crate::leanh::lean_dec(v_unused_2892_);
                            v_unused_2893_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                            crate::leanh::lean_dec(v_unused_2893_);
                            v_unused_2894_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                            crate::leanh::lean_dec(v_unused_2894_);
                            v_unused_2895_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                            crate::leanh::lean_dec(v_unused_2895_);
                            v___x_2868_ = v_l_2447_;
                            v_isShared_2869_ = v_isSharedCheck_2890_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_2447_);
                            v___x_2868_ = crate::leanh::lean_box(0);
                            v_isShared_2869_ = v_isSharedCheck_2890_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_2631_) == 0 {
                            crate::leanh::lean_inc(v_l_2630_);
                            crate::leanh::lean_inc(v_v_2629_);
                            crate::leanh::lean_inc(v_k_2628_);
                            v_isSharedCheck_2920_ =
                                (!crate::leanh::lean_is_exclusive(v_l_2447_)) as u8;
                            if v_isSharedCheck_2920_ == 0 {
                                v_unused_2921_ = crate::leanh::lean_ctor_get(v_l_2447_, 4);
                                crate::leanh::lean_dec(v_unused_2921_);
                                v_unused_2922_ = crate::leanh::lean_ctor_get(v_l_2447_, 3);
                                crate::leanh::lean_dec(v_unused_2922_);
                                v_unused_2923_ = crate::leanh::lean_ctor_get(v_l_2447_, 2);
                                crate::leanh::lean_dec(v_unused_2923_);
                                v_unused_2924_ = crate::leanh::lean_ctor_get(v_l_2447_, 1);
                                crate::leanh::lean_dec(v_unused_2924_);
                                v_unused_2925_ = crate::leanh::lean_ctor_get(v_l_2447_, 0);
                                crate::leanh::lean_dec(v_unused_2925_);
                                v___x_2897_ = v_l_2447_;
                                v_isShared_2898_ = v_isSharedCheck_2920_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_2447_);
                                v___x_2897_ = crate::leanh::lean_box(0);
                                v_isShared_2898_ = v_isSharedCheck_2920_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_2926_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                            crate::leanh::lean_inc(v_k_2926_);
                            v_v_2927_ = crate::leanh::lean_ctor_get(v___x_2783_, 1);
                            crate::leanh::lean_inc(v_v_2927_);
                            crate::leanh::lean_dec_ref(v___x_2783_);
                            v___x_2928_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2782_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2781_, 4, v_r_2631_);
                                crate::leanh::lean_ctor_set(v___x_2781_, 3, v_l_2447_);
                                crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2927_);
                                crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2926_);
                                crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2928_);
                                v___x_2930_ = v___x_2781_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_2931_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2928_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_k_2926_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 2, v_v_2927_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 3, v_l_2447_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 4, v_r_2631_);
                                v___x_2930_ = v_reuseFailAlloc_2931_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_2794_;
            }
            53 => {
                v_size_2799_ = crate::leanh::lean_ctor_get(v_l_2630_, 0);
                v_size_2800_ = crate::leanh::lean_ctor_get(v_r_2631_, 0);
                v_k_2801_ = crate::leanh::lean_ctor_get(v_r_2631_, 1);
                v_v_2802_ = crate::leanh::lean_ctor_get(v_r_2631_, 2);
                v_l_2803_ = crate::leanh::lean_ctor_get(v_r_2631_, 3);
                v_r_2804_ = crate::leanh::lean_ctor_get(v_r_2631_, 4);
                v___x_2805_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2806_ = lean_nat_mul(v___x_2805_, v_size_2799_);
                v___x_2807_ = lean_nat_dec_lt(v_size_2800_, v___x_2806_);
                crate::leanh::lean_dec(v___x_2806_);
                if v___x_2807_ == 0 {
                    crate::leanh::lean_inc(v_r_2804_);
                    crate::leanh::lean_inc(v_l_2803_);
                    crate::leanh::lean_inc(v_v_2802_);
                    crate::leanh::lean_inc(v_k_2801_);
                    crate::leanh::lean_del_object(v___x_2797_);
                    v_isSharedCheck_2845_ = (!crate::leanh::lean_is_exclusive(v_r_2631_)) as u8;
                    if v_isSharedCheck_2845_ == 0 {
                        v_unused_2846_ = crate::leanh::lean_ctor_get(v_r_2631_, 4);
                        crate::leanh::lean_dec(v_unused_2846_);
                        v_unused_2847_ = crate::leanh::lean_ctor_get(v_r_2631_, 3);
                        crate::leanh::lean_dec(v_unused_2847_);
                        v_unused_2848_ = crate::leanh::lean_ctor_get(v_r_2631_, 2);
                        crate::leanh::lean_dec(v_unused_2848_);
                        v_unused_2849_ = crate::leanh::lean_ctor_get(v_r_2631_, 1);
                        crate::leanh::lean_dec(v_unused_2849_);
                        v_unused_2850_ = crate::leanh::lean_ctor_get(v_r_2631_, 0);
                        crate::leanh::lean_dec(v_unused_2850_);
                        v___x_2809_ = v_r_2631_;
                        v_isShared_2810_ = v_isSharedCheck_2845_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2631_);
                        v___x_2809_ = crate::leanh::lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2845_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_2851_ = lean_nat_add(v___x_2637_, v_size_2627_);
                    crate::leanh::lean_dec(v_size_2627_);
                    v___x_2852_ = lean_nat_add(v___x_2851_, v_size_2787_);
                    crate::leanh::lean_dec(v___x_2851_);
                    v___x_2853_ = lean_nat_add(v___x_2637_, v_size_2787_);
                    v___x_2854_ = lean_nat_add(v___x_2853_, v_size_2800_);
                    crate::leanh::lean_dec(v___x_2853_);
                    if v_isShared_2782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2781_, 4, v_tree_2784_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2786_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2785_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2854_);
                        v___x_2856_ = v___x_2781_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2854_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_k_2785_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_v_2786_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 4, v_tree_2784_);
                        v___x_2856_ = v_reuseFailAlloc_2860_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_2811_ = lean_nat_add(v___x_2637_, v_size_2627_);
                crate::leanh::lean_dec(v_size_2627_);
                v___x_2812_ = lean_nat_add(v___x_2811_, v_size_2787_);
                crate::leanh::lean_dec(v___x_2811_);
                v___x_2833_ = lean_nat_add(v___x_2637_, v_size_2799_);
                if crate::leanh::lean_obj_tag(v_l_2803_) == 0 {
                    v_size_2843_ = crate::leanh::lean_ctor_get(v_l_2803_, 0);
                    crate::leanh::lean_inc(v_size_2843_);
                    v___y_2835_ = v_size_2843_;
                    state = 59;
                    continue;
                } else {
                    v___x_2844_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2835_ = v___x_2844_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_2817_ = lean_nat_add(v___y_2815_, v___y_2816_);
                crate::leanh::lean_dec(v___y_2816_);
                crate::leanh::lean_dec(v___y_2815_);
                crate::leanh::lean_inc_ref(v_tree_2784_);
                if v_isShared_2810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2809_, 4, v_tree_2784_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 3, v_r_2804_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 2, v_v_2786_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 1, v_k_2785_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 0, v___x_2817_);
                    v___x_2819_ = v___x_2809_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2817_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 3, v_r_2804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 4, v_tree_2784_);
                    v___x_2819_ = v_reuseFailAlloc_2832_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_2826_ = (!crate::leanh::lean_is_exclusive(v_tree_2784_)) as u8;
                if v_isSharedCheck_2826_ == 0 {
                    v_unused_2827_ = crate::leanh::lean_ctor_get(v_tree_2784_, 4);
                    crate::leanh::lean_dec(v_unused_2827_);
                    v_unused_2828_ = crate::leanh::lean_ctor_get(v_tree_2784_, 3);
                    crate::leanh::lean_dec(v_unused_2828_);
                    v_unused_2829_ = crate::leanh::lean_ctor_get(v_tree_2784_, 2);
                    crate::leanh::lean_dec(v_unused_2829_);
                    v_unused_2830_ = crate::leanh::lean_ctor_get(v_tree_2784_, 1);
                    crate::leanh::lean_dec(v_unused_2830_);
                    v_unused_2831_ = crate::leanh::lean_ctor_get(v_tree_2784_, 0);
                    crate::leanh::lean_dec(v_unused_2831_);
                    v___x_2821_ = v_tree_2784_;
                    v_isShared_2822_ = v_isSharedCheck_2826_;
                    state = 57;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_2784_);
                    v___x_2821_ = crate::leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2826_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_2822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2821_, 4, v___x_2819_);
                    crate::leanh::lean_ctor_set(v___x_2821_, 3, v___y_2814_);
                    crate::leanh::lean_ctor_set(v___x_2821_, 2, v_v_2802_);
                    crate::leanh::lean_ctor_set(v___x_2821_, 1, v_k_2801_);
                    crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2812_);
                    v___x_2824_ = v___x_2821_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_k_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_v_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 3, v___y_2814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 4, v___x_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2825_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_2824_;
            }
            59 => {
                v___x_2836_ = lean_nat_add(v___x_2833_, v___y_2835_);
                crate::leanh::lean_dec(v___y_2835_);
                crate::leanh::lean_dec(v___x_2833_);
                if v_isShared_2782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2781_, 4, v_l_2803_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2836_);
                    v___x_2838_ = v___x_2781_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2842_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_l_2803_);
                    v___x_2838_ = v_reuseFailAlloc_2842_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2839_ = lean_nat_add(v___x_2637_, v_size_2787_);
                if crate::leanh::lean_obj_tag(v_r_2804_) == 0 {
                    v_size_2840_ = crate::leanh::lean_ctor_get(v_r_2804_, 0);
                    crate::leanh::lean_inc(v_size_2840_);
                    v___y_2814_ = v___x_2838_;
                    v___y_2815_ = v___x_2839_;
                    v___y_2816_ = v_size_2840_;
                    state = 55;
                    continue;
                } else {
                    v___x_2841_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2814_ = v___x_2838_;
                    v___y_2815_ = v___x_2839_;
                    v___y_2816_ = v___x_2841_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_2798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2797_, 4, v___x_2856_);
                    crate::leanh::lean_ctor_set(v___x_2797_, 0, v___x_2852_);
                    v___x_2858_ = v___x_2797_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 4, v___x_2856_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_2858_;
            }
            63 => {
                if crate::leanh::lean_obj_tag(v_r_2631_) == 0 {
                    v_k_2870_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    crate::leanh::lean_inc(v_k_2870_);
                    v_v_2871_ = crate::leanh::lean_ctor_get(v___x_2783_, 1);
                    crate::leanh::lean_inc(v_v_2871_);
                    crate::leanh::lean_dec_ref(v___x_2783_);
                    v_size_2872_ = crate::leanh::lean_ctor_get(v_r_2631_, 0);
                    v___x_2873_ = lean_nat_add(v___x_2637_, v_size_2627_);
                    crate::leanh::lean_dec(v_size_2627_);
                    v___x_2874_ = lean_nat_add(v___x_2637_, v_size_2872_);
                    if v_isShared_2782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2781_, 4, v_tree_2784_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2871_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2870_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2874_);
                        v___x_2876_ = v___x_2781_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2880_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_k_2870_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_v_2871_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_tree_2784_);
                        v___x_2876_ = v_reuseFailAlloc_2880_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_2627_);
                    v_k_2881_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                    crate::leanh::lean_inc(v_k_2881_);
                    v_v_2882_ = crate::leanh::lean_ctor_get(v___x_2783_, 1);
                    crate::leanh::lean_inc(v_v_2882_);
                    crate::leanh::lean_dec_ref(v___x_2783_);
                    v___x_2883_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_2782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2781_, 4, v_r_2631_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2882_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2881_);
                        crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2637_);
                        v___x_2885_ = v___x_2781_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_2889_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2637_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2881_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2882_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_r_2631_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_r_2631_);
                        v___x_2885_ = v_reuseFailAlloc_2889_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2868_, 4, v___x_2876_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2873_);
                    v___x_2878_ = v___x_2868_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2879_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 4, v___x_2876_);
                    v___x_2878_ = v_reuseFailAlloc_2879_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2878_;
            }
            66 => {
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2868_, 4, v___x_2885_);
                    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2883_);
                    v___x_2887_ = v___x_2868_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_2888_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2888_, 4, v___x_2885_);
                    v___x_2887_ = v_reuseFailAlloc_2888_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_2887_;
            }
            68 => {
                v_k_2899_ = crate::leanh::lean_ctor_get(v___x_2783_, 0);
                crate::leanh::lean_inc(v_k_2899_);
                v_v_2900_ = crate::leanh::lean_ctor_get(v___x_2783_, 1);
                crate::leanh::lean_inc(v_v_2900_);
                crate::leanh::lean_dec_ref(v___x_2783_);
                v_k_2901_ = crate::leanh::lean_ctor_get(v_r_2631_, 1);
                v_v_2902_ = crate::leanh::lean_ctor_get(v_r_2631_, 2);
                v_isSharedCheck_2916_ = (!crate::leanh::lean_is_exclusive(v_r_2631_)) as u8;
                if v_isSharedCheck_2916_ == 0 {
                    v_unused_2917_ = crate::leanh::lean_ctor_get(v_r_2631_, 4);
                    crate::leanh::lean_dec(v_unused_2917_);
                    v_unused_2918_ = crate::leanh::lean_ctor_get(v_r_2631_, 3);
                    crate::leanh::lean_dec(v_unused_2918_);
                    v_unused_2919_ = crate::leanh::lean_ctor_get(v_r_2631_, 0);
                    crate::leanh::lean_dec(v_unused_2919_);
                    v___x_2904_ = v_r_2631_;
                    v_isShared_2905_ = v_isSharedCheck_2916_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2902_);
                    crate::leanh::lean_inc(v_k_2901_);
                    crate::leanh::lean_dec(v_r_2631_);
                    v___x_2904_ = crate::leanh::lean_box(0);
                    v_isShared_2905_ = v_isSharedCheck_2916_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_2906_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2905_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2904_, 4, v_l_2630_);
                    crate::leanh::lean_ctor_set(v___x_2904_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v___x_2904_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v___x_2904_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v___x_2904_, 0, v___x_2637_);
                    v___x_2908_ = v___x_2904_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_k_2628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_v_2629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_l_2630_);
                    v___x_2908_ = v_reuseFailAlloc_2915_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_2782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2781_, 4, v_l_2630_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 2, v_v_2900_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 1, v_k_2899_);
                    crate::leanh::lean_ctor_set(v___x_2781_, 0, v___x_2637_);
                    v___x_2910_ = v___x_2781_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_k_2899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_v_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_l_2630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_l_2630_);
                    v___x_2910_ = v_reuseFailAlloc_2914_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_2898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2897_, 4, v___x_2910_);
                    crate::leanh::lean_ctor_set(v___x_2897_, 3, v___x_2908_);
                    crate::leanh::lean_ctor_set(v___x_2897_, 2, v_v_2902_);
                    crate::leanh::lean_ctor_set(v___x_2897_, 1, v_k_2901_);
                    crate::leanh::lean_ctor_set(v___x_2897_, 0, v___x_2906_);
                    v___x_2912_ = v___x_2897_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 3, v___x_2908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 4, v___x_2910_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_2912_;
            }
            73 => {
                return v___x_2930_;
            }
            74 => {
                return v___x_2952_;
            }
            75 => {
                v_size_2957_ = crate::leanh::lean_ctor_get(v_l_2944_, 0);
                v_size_2958_ = crate::leanh::lean_ctor_get(v_r_2945_, 0);
                v_k_2959_ = crate::leanh::lean_ctor_get(v_r_2945_, 1);
                v_v_2960_ = crate::leanh::lean_ctor_get(v_r_2945_, 2);
                v_l_2961_ = crate::leanh::lean_ctor_get(v_r_2945_, 3);
                v_r_2962_ = crate::leanh::lean_ctor_get(v_r_2945_, 4);
                v___x_2963_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2964_ = lean_nat_mul(v___x_2963_, v_size_2957_);
                v___x_2965_ = lean_nat_dec_lt(v_size_2958_, v___x_2964_);
                crate::leanh::lean_dec(v___x_2964_);
                if v___x_2965_ == 0 {
                    crate::leanh::lean_inc(v_r_2962_);
                    crate::leanh::lean_inc(v_l_2961_);
                    crate::leanh::lean_inc(v_v_2960_);
                    crate::leanh::lean_inc(v_k_2959_);
                    v_isSharedCheck_2994_ = (!crate::leanh::lean_is_exclusive(v_r_2945_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v_unused_2995_ = crate::leanh::lean_ctor_get(v_r_2945_, 4);
                        crate::leanh::lean_dec(v_unused_2995_);
                        v_unused_2996_ = crate::leanh::lean_ctor_get(v_r_2945_, 3);
                        crate::leanh::lean_dec(v_unused_2996_);
                        v_unused_2997_ = crate::leanh::lean_ctor_get(v_r_2945_, 2);
                        crate::leanh::lean_dec(v_unused_2997_);
                        v_unused_2998_ = crate::leanh::lean_ctor_get(v_r_2945_, 1);
                        crate::leanh::lean_dec(v_unused_2998_);
                        v_unused_2999_ = crate::leanh::lean_ctor_get(v_r_2945_, 0);
                        crate::leanh::lean_dec(v_unused_2999_);
                        v___x_2967_ = v_r_2945_;
                        v_isShared_2968_ = v_isSharedCheck_2994_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2945_);
                        v___x_2967_ = crate::leanh::lean_box(0);
                        v_isShared_2968_ = v_isSharedCheck_2994_;
                        state = 76;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2450_);
                    v___x_3000_ = lean_nat_add(v___x_2939_, v_size_2941_);
                    crate::leanh::lean_dec(v_size_2941_);
                    v___x_3001_ = lean_nat_add(v___x_3000_, v_size_2940_);
                    crate::leanh::lean_dec(v___x_3000_);
                    v___x_3002_ = lean_nat_add(v___x_2939_, v_size_2940_);
                    crate::leanh::lean_dec(v_size_2940_);
                    v___x_3003_ = lean_nat_add(v___x_3002_, v_size_2958_);
                    crate::leanh::lean_dec(v___x_3002_);
                    crate::leanh::lean_inc_ref(v_impl_2938_);
                    if v_isShared_2956_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2955_, 4, v_impl_2938_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 3, v_r_2945_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 2, v_v_2446_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 1, v_k_2445_);
                        crate::leanh::lean_ctor_set(v___x_2955_, 0, v___x_3003_);
                        v___x_3005_ = v___x_2955_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_3018_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3003_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_k_2445_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_v_2446_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_r_2945_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 4, v_impl_2938_);
                        v___x_3005_ = v_reuseFailAlloc_3018_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_2969_ = lean_nat_add(v___x_2939_, v_size_2941_);
                crate::leanh::lean_dec(v_size_2941_);
                v___x_2970_ = lean_nat_add(v___x_2969_, v_size_2940_);
                crate::leanh::lean_dec(v___x_2969_);
                v___x_2982_ = lean_nat_add(v___x_2939_, v_size_2957_);
                if crate::leanh::lean_obj_tag(v_l_2961_) == 0 {
                    v_size_2992_ = crate::leanh::lean_ctor_get(v_l_2961_, 0);
                    crate::leanh::lean_inc(v_size_2992_);
                    v___y_2984_ = v_size_2992_;
                    state = 80;
                    continue;
                } else {
                    v___x_2993_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2984_ = v___x_2993_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_2975_ = lean_nat_add(v___y_2973_, v___y_2974_);
                crate::leanh::lean_dec(v___y_2974_);
                crate::leanh::lean_dec(v___y_2973_);
                if v_isShared_2968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2967_, 4, v_impl_2938_);
                    crate::leanh::lean_ctor_set(v___x_2967_, 3, v_r_2962_);
                    crate::leanh::lean_ctor_set(v___x_2967_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_2967_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_2967_, 0, v___x_2975_);
                    v___x_2977_ = v___x_2967_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 3, v_r_2962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 4, v_impl_2938_);
                    v___x_2977_ = v_reuseFailAlloc_2981_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_2956_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2955_, 4, v___x_2977_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 3, v___y_2972_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 2, v_v_2960_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 1, v_k_2959_);
                    crate::leanh::lean_ctor_set(v___x_2955_, 0, v___x_2970_);
                    v___x_2979_ = v___x_2955_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2980_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_k_2959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 2, v_v_2960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 3, v___y_2972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2980_, 4, v___x_2977_);
                    v___x_2979_ = v_reuseFailAlloc_2980_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_2979_;
            }
            80 => {
                v___x_2985_ = lean_nat_add(v___x_2982_, v___y_2984_);
                crate::leanh::lean_dec(v___y_2984_);
                crate::leanh::lean_dec(v___x_2982_);
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v_l_2961_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_l_2944_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_2943_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_2942_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_2985_);
                    v___x_2987_ = v___x_2450_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v___x_2985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_k_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 2, v_v_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 3, v_l_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 4, v_l_2961_);
                    v___x_2987_ = v_reuseFailAlloc_2991_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_2988_ = lean_nat_add(v___x_2939_, v_size_2940_);
                crate::leanh::lean_dec(v_size_2940_);
                if crate::leanh::lean_obj_tag(v_r_2962_) == 0 {
                    v_size_2989_ = crate::leanh::lean_ctor_get(v_r_2962_, 0);
                    crate::leanh::lean_inc(v_size_2989_);
                    v___y_2972_ = v___x_2987_;
                    v___y_2973_ = v___x_2988_;
                    v___y_2974_ = v_size_2989_;
                    state = 77;
                    continue;
                } else {
                    v___x_2990_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2972_ = v___x_2987_;
                    v___y_2973_ = v___x_2988_;
                    v___y_2974_ = v___x_2990_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_3012_ = (!crate::leanh::lean_is_exclusive(v_impl_2938_)) as u8;
                if v_isSharedCheck_3012_ == 0 {
                    v_unused_3013_ = crate::leanh::lean_ctor_get(v_impl_2938_, 4);
                    crate::leanh::lean_dec(v_unused_3013_);
                    v_unused_3014_ = crate::leanh::lean_ctor_get(v_impl_2938_, 3);
                    crate::leanh::lean_dec(v_unused_3014_);
                    v_unused_3015_ = crate::leanh::lean_ctor_get(v_impl_2938_, 2);
                    crate::leanh::lean_dec(v_unused_3015_);
                    v_unused_3016_ = crate::leanh::lean_ctor_get(v_impl_2938_, 1);
                    crate::leanh::lean_dec(v_unused_3016_);
                    v_unused_3017_ = crate::leanh::lean_ctor_get(v_impl_2938_, 0);
                    crate::leanh::lean_dec(v_unused_3017_);
                    v___x_3007_ = v_impl_2938_;
                    v_isShared_3008_ = v_isSharedCheck_3012_;
                    state = 83;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_2938_);
                    v___x_3007_ = crate::leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3012_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_3008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3007_, 4, v___x_3005_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 3, v_l_2944_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 2, v_v_2943_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 1, v_k_2942_);
                    crate::leanh::lean_ctor_set(v___x_3007_, 0, v___x_3001_);
                    v___x_3010_ = v___x_3007_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_3001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v_k_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 2, v_v_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 3, v_l_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 4, v___x_3005_);
                    v___x_3010_ = v_reuseFailAlloc_3011_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_3010_;
            }
            85 => {
                return v___x_3028_;
            }
            86 => {
                v_size_3038_ = crate::leanh::lean_ctor_get(v_r_3031_, 0);
                v___x_3039_ = lean_nat_add(v___x_2939_, v_size_3032_);
                crate::leanh::lean_dec(v_size_3032_);
                v___x_3040_ = lean_nat_add(v___x_2939_, v_size_3038_);
                if v_isShared_3037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3036_, 4, v_impl_2938_);
                    crate::leanh::lean_ctor_set(v___x_3036_, 3, v_r_3031_);
                    crate::leanh::lean_ctor_set(v___x_3036_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_3036_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_3036_, 0, v___x_3040_);
                    v___x_3042_ = v___x_3036_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_r_3031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 4, v_impl_2938_);
                    v___x_3042_ = v_reuseFailAlloc_3046_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v___x_3042_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_3034_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_3033_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_3039_);
                    v___x_3044_ = v___x_2450_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_k_3033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_v_3034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 4, v___x_3042_);
                    v___x_3044_ = v_reuseFailAlloc_3045_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_3044_;
            }
            89 => {
                v___x_3055_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3053_, 3, v_r_3031_);
                    crate::leanh::lean_ctor_set(v___x_3053_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_3053_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_3053_, 0, v___x_2939_);
                    v___x_3057_ = v___x_3053_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_r_3031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 4, v_r_3031_);
                    v___x_3057_ = v_reuseFailAlloc_3061_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v___x_3057_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_3051_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_3050_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_3055_);
                    v___x_3059_ = v___x_2450_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_k_3050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_v_3051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 4, v___x_3057_);
                    v___x_3059_ = v_reuseFailAlloc_3060_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_3059_;
            }
            92 => {
                v_k_3072_ = crate::leanh::lean_ctor_get(v_r_3066_, 1);
                v_v_3073_ = crate::leanh::lean_ctor_get(v_r_3066_, 2);
                v_isSharedCheck_3087_ = (!crate::leanh::lean_is_exclusive(v_r_3066_)) as u8;
                if v_isSharedCheck_3087_ == 0 {
                    v_unused_3088_ = crate::leanh::lean_ctor_get(v_r_3066_, 4);
                    crate::leanh::lean_dec(v_unused_3088_);
                    v_unused_3089_ = crate::leanh::lean_ctor_get(v_r_3066_, 3);
                    crate::leanh::lean_dec(v_unused_3089_);
                    v_unused_3090_ = crate::leanh::lean_ctor_get(v_r_3066_, 0);
                    crate::leanh::lean_dec(v_unused_3090_);
                    v___x_3075_ = v_r_3066_;
                    v_isShared_3076_ = v_isSharedCheck_3087_;
                    state = 93;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3073_);
                    crate::leanh::lean_inc(v_k_3072_);
                    crate::leanh::lean_dec(v_r_3066_);
                    v___x_3075_ = crate::leanh::lean_box(0);
                    v_isShared_3076_ = v_isSharedCheck_3087_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_3077_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3076_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3075_, 4, v_l_3030_);
                    crate::leanh::lean_ctor_set(v___x_3075_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v___x_3075_, 2, v_v_3068_);
                    crate::leanh::lean_ctor_set(v___x_3075_, 1, v_k_3067_);
                    crate::leanh::lean_ctor_set(v___x_3075_, 0, v___x_2939_);
                    v___x_3079_ = v___x_3075_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_3086_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_k_3067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_v_3068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_l_3030_);
                    v___x_3079_ = v_reuseFailAlloc_3086_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_3071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3070_, 4, v_l_3030_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v___x_3070_, 0, v___x_2939_);
                    v___x_3081_ = v___x_3070_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_k_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_v_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_l_3030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 4, v_l_3030_);
                    v___x_3081_ = v_reuseFailAlloc_3085_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_2451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2450_, 4, v___x_3081_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 3, v___x_3079_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 2, v_v_3073_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 1, v_k_3072_);
                    crate::leanh::lean_ctor_set(v___x_2450_, 0, v___x_3077_);
                    v___x_3083_ = v___x_2450_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_k_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_v_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 3, v___x_3079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 4, v___x_3081_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_3083_;
            }
            97 => {
                return v___x_3097_;
            }
            98 => {
                return v___x_3100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg___boxed(
    mut v_k_3104_: *mut crate::leanh::LeanObject,
    mut v_t_3105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_3104_, v_t_3105_);
    crate::leanh::lean_dec(v_k_3104_);
    return v_res_3106_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(
    mut v_init_3107_: *mut crate::leanh::LeanObject,
    mut v_x_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3108_) == 0 {
                    v_k_3109_ = crate::leanh::lean_ctor_get(v_x_3108_, 1);
                    v_l_3110_ = crate::leanh::lean_ctor_get(v_x_3108_, 3);
                    v_r_3111_ = crate::leanh::lean_ctor_get(v_x_3108_, 4);
                    v___x_3112_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_3107_, v_l_3110_);
                    v___x_3113_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_3109_, v___x_3112_);
                    v_init_3107_ = v___x_3113_;
                    v_x_3108_ = v_r_3111_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3107_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5___boxed(
    mut v_init_3115_: *mut crate::leanh::LeanObject,
    mut v_x_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3117_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_3115_, v_x_3116_);
    crate::leanh::lean_dec(v_x_3116_);
    return v_res_3117_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(
    mut v_candidate_3118_: *mut crate::leanh::LeanObject,
    mut v_init_3119_: *mut crate::leanh::LeanObject,
    mut v_x_3120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3120_) == 0 {
                    v_k_3121_ = crate::leanh::lean_ctor_get(v_x_3120_, 1);
                    crate::leanh::lean_inc(v_k_3121_);
                    v_l_3122_ = crate::leanh::lean_ctor_get(v_x_3120_, 3);
                    crate::leanh::lean_inc(v_l_3122_);
                    v_r_3123_ = crate::leanh::lean_ctor_get(v_x_3120_, 4);
                    crate::leanh::lean_inc(v_r_3123_);
                    crate::leanh::lean_dec_ref_known(v_x_3120_, 5);
                    v___x_3124_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_3118_, v_init_3119_, v_l_3122_);
                    v___x_3125_ = l_Lean_NameSet_contains(v_candidate_3118_, v_k_3121_);
                    if v___x_3125_ == 0 {
                        crate::leanh::lean_dec(v_k_3121_);
                        v_init_3119_ = v___x_3124_;
                        v_x_3120_ = v_r_3123_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3127_ = l_Lean_NameSet_insert(v___x_3124_, v_k_3121_);
                        v_init_3119_ = v___x_3127_;
                        v_x_3120_ = v_r_3123_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_init_3119_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0___boxed(
    mut v_candidate_3129_: *mut crate::leanh::LeanObject,
    mut v_init_3130_: *mut crate::leanh::LeanObject,
    mut v_x_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3132_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_3129_, v_init_3130_, v_x_3131_);
    crate::leanh::lean_dec(v_candidate_3129_);
    return v_res_3132_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(
    mut v_weight_3133_: *mut crate::leanh::LeanObject,
    mut v_init_3134_: f64,
    mut v_x_3135_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v_k_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: f64 = 0.0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: f64 = 0.0;
    let mut v___x_3142_: f64 = 0.0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3135_) == 0 {
                    v_k_3136_ = crate::leanh::lean_ctor_get(v_x_3135_, 1);
                    crate::leanh::lean_inc(v_k_3136_);
                    v_l_3137_ = crate::leanh::lean_ctor_get(v_x_3135_, 3);
                    crate::leanh::lean_inc(v_l_3137_);
                    v_r_3138_ = crate::leanh::lean_ctor_get(v_x_3135_, 4);
                    crate::leanh::lean_inc(v_r_3138_);
                    crate::leanh::lean_dec_ref_known(v_x_3135_, 5);
                    crate::leanh::lean_inc_ref_n(v_weight_3133_, 2);
                    v___x_3139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_3133_, v_init_3134_, v_l_3137_);
                    v___x_3140_ = crate::leanh::lean_apply_1(v_weight_3133_, v_k_3136_);
                    v___x_3141_ = crate::leanh::lean_unbox_float(v___x_3140_);
                    crate::leanh::lean_dec_ref(v___x_3140_);
                    v___x_3142_ = lean_float_add(v___x_3139_, v___x_3141_);
                    v_init_3134_ = v___x_3142_;
                    v_x_3135_ = v_r_3138_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_weight_3133_);
                    return v_init_3134_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2___boxed(
    mut v_weight_3144_: *mut crate::leanh::LeanObject,
    mut v_init_3145_: *mut crate::leanh::LeanObject,
    mut v_x_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_boxed_3147_: f64 = 0.0;
    let mut v_res_3148_: f64 = 0.0;
    let mut v_r_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_init_boxed_3147_ = crate::leanh::lean_unbox_float(v_init_3145_);
    crate::leanh::lean_dec_ref(v_init_3145_);
    v_res_3148_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_3144_, v_init_boxed_3147_, v_x_3146_);
    v_r_3149_ = crate::leanh::lean_box_float(v_res_3148_);
    return v_r_3149_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0()
-> f64 {
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: f64 = 0.0;
    v___x_3150_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3151_ = lean_float_of_nat(v___x_3150_);
    return v___x_3151_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(
    mut v_weight_3152_: *mut crate::leanh::LeanObject,
    mut v_relevant_3153_: *mut crate::leanh::LeanObject,
    mut v_candidate_3154_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_R_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_R_x27_3159_: f64 = 0.0;
    let mut v___x_3160_: f64 = 0.0;
    let mut v_M_3161_: f64 = 0.0;
    let mut v___x_3162_: f64 = 0.0;
    let mut v___x_3163_: f64 = 0.0;
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3155_ = l_Lean_NameSet_empty;
                v_R_3156_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_3154_, v___x_3155_, v_relevant_3153_);
                v___x_3164_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_candidate_3154_, v_R_3156_);
                if crate::leanh::lean_obj_tag(v___x_3164_) == 0 {
                    v_size_3165_ = crate::leanh::lean_ctor_get(v___x_3164_, 0);
                    crate::leanh::lean_inc(v_size_3165_);
                    crate::leanh::lean_dec_ref_known(v___x_3164_, 5);
                    v___y_3158_ = v_size_3165_;
                    state = 1;
                    continue;
                } else {
                    v___x_3166_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3158_ = v___x_3166_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_R_x27_3159_ = lean_float_of_nat(v___y_3158_);
                v___x_3160_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once), _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0);
                v_M_3161_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_3152_, v___x_3160_, v_R_3156_);
                v___x_3162_ = lean_float_add(v_M_3161_, v_R_x27_3159_);
                v___x_3163_ = lean_float_div(v_M_3161_, v___x_3162_);
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___boxed(
    mut v_weight_3167_: *mut crate::leanh::LeanObject,
    mut v_relevant_3168_: *mut crate::leanh::LeanObject,
    mut v_candidate_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3170_: f64 = 0.0;
    let mut v_r_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(
            v_weight_3167_,
            v_relevant_3168_,
            v_candidate_3169_,
        );
    v_r_3171_ = crate::leanh::lean_box_float(v_res_3170_);
    return v_r_3171_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0(
    mut v_candidate_3172_: *mut crate::leanh::LeanObject,
    mut v_init_3173_: *mut crate::leanh::LeanObject,
    mut v_t_3174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3175_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0_spec__0(v_candidate_3172_, v_init_3173_, v_t_3174_);
    return v___x_3175_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0___boxed(
    mut v_candidate_3176_: *mut crate::leanh::LeanObject,
    mut v_init_3177_: *mut crate::leanh::LeanObject,
    mut v_t_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__0(v_candidate_3176_, v_init_3177_, v_t_3178_);
    crate::leanh::lean_dec(v_candidate_3176_);
    return v_res_3179_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1(
    mut v_weight_3180_: *mut crate::leanh::LeanObject,
    mut v_init_3181_: f64,
    mut v_t_3182_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_3183_: f64 = 0.0;
    v___x_3183_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1_spec__2(v_weight_3180_, v_init_3181_, v_t_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1___boxed(
    mut v_weight_3184_: *mut crate::leanh::LeanObject,
    mut v_init_3185_: *mut crate::leanh::LeanObject,
    mut v_t_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_boxed_3187_: f64 = 0.0;
    let mut v_res_3188_: f64 = 0.0;
    let mut v_r_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_init_boxed_3187_ = crate::leanh::lean_unbox_float(v_init_3185_);
    crate::leanh::lean_dec_ref(v_init_3185_);
    v_res_3188_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__1(v_weight_3184_, v_init_boxed_3187_, v_t_3186_);
    v_r_3189_ = crate::leanh::lean_box_float(v_res_3188_);
    return v_r_3189_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2(
    mut v_00_u03b2_3190_: *mut crate::leanh::LeanObject,
    mut v_k_3191_: *mut crate::leanh::LeanObject,
    mut v_t_3192_: *mut crate::leanh::LeanObject,
    mut v_h_3193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___redArg(v_k_3191_, v_t_3192_);
    return v___x_3194_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2___boxed(
    mut v_00_u03b2_3195_: *mut crate::leanh::LeanObject,
    mut v_k_3196_: *mut crate::leanh::LeanObject,
    mut v_t_3197_: *mut crate::leanh::LeanObject,
    mut v_h_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__2(v_00_u03b2_3195_, v_k_3196_, v_t_3197_, v_h_3198_);
    crate::leanh::lean_dec(v_k_3196_);
    return v_res_3199_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3(
    mut v_init_3200_: *mut crate::leanh::LeanObject,
    mut v_t_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3_spec__5(v_init_3200_, v_t_3201_);
    return v___x_3202_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3___boxed(
    mut v_init_3203_: *mut crate::leanh::LeanObject,
    mut v_t_3204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3205_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore_spec__3(v_init_3203_, v_t_3204_);
    crate::leanh::lean_dec(v_t_3204_);
    return v_res_3205_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0()
-> f64 {
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: f64 = 0.0;
    v___x_3206_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3207_ = 1;
    v___x_3208_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_3209_ = l_Float_ofScientific(v___x_3208_, v___x_3207_, v___x_3206_);
    return v___x_3209_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1()
-> f64 {
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: f64 = 0.0;
    v___x_3210_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3211_ = 1;
    v___x_3212_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_3213_ = l_Float_ofScientific(v___x_3212_, v___x_3211_, v___x_3210_);
    return v___x_3213_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(
    mut v_n_3214_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_3215_: f64 = 0.0;
    let mut v___x_3216_: f64 = 0.0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: f64 = 0.0;
    let mut v___x_3219_: f64 = 0.0;
    let mut v___x_3220_: f64 = 0.0;
    let mut v___x_3221_: f64 = 0.0;
    v___x_3215_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0_once), _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__0);
    v___x_3216_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1_once), _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___closed__1);
    v___x_3217_ = lean_nat_log2(v_n_3214_);
    v___x_3218_ = lean_float_of_nat(v___x_3217_);
    v___x_3219_ = lean_float_add(v___x_3218_, v___x_3215_);
    v___x_3220_ = lean_float_div(v___x_3216_, v___x_3219_);
    v___x_3221_ = lean_float_add(v___x_3215_, v___x_3220_);
    return v___x_3221_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction___boxed(
    mut v_n_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: f64 = 0.0;
    let mut v_r_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(
            v_n_3222_,
        );
    crate::leanh::lean_dec(v_n_3222_);
    v_r_3224_ = crate::leanh::lean_box_float(v_res_3223_);
    return v_r_3224_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0(
    mut v_frequency_3225_: *mut crate::leanh::LeanObject,
    mut v_n_3226_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: f64 = 0.0;
    v___x_3227_ = crate::leanh::lean_apply_1(v_frequency_3225_, v_n_3226_);
    v___x_3228_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightFunction(
            v___x_3227_,
        );
    crate::leanh::lean_dec(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0___boxed(
    mut v_frequency_3229_: *mut crate::leanh::LeanObject,
    mut v_n_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3231_: f64 = 0.0;
    let mut v_r_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3231_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0(v_frequency_3229_, v_n_3230_);
    v_r_3232_ = crate::leanh::lean_box_float(v_res_3231_);
    return v_r_3232_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore(
    mut v_frequency_3233_: *mut crate::leanh::LeanObject,
    mut v_relevant_3234_: *mut crate::leanh::LeanObject,
    mut v_candidate_3235_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___f_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: f64 = 0.0;
    v___f_3236_ = crate::leanh::lean_alloc_closure(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_3236_, 0, v_frequency_3233_);
    v___x_3237_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(
            v___f_3236_,
            v_relevant_3234_,
            v_candidate_3235_,
        );
    return v___x_3237_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___boxed(
    mut v_frequency_3238_: *mut crate::leanh::LeanObject,
    mut v_relevant_3239_: *mut crate::leanh::LeanObject,
    mut v_candidate_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: f64 = 0.0;
    let mut v_r_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore(
            v_frequency_3238_,
            v_relevant_3239_,
            v_candidate_3240_,
        );
    v_r_3242_ = crate::leanh::lean_box_float(v_res_3241_);
    return v_r_3242_;
}
pub unsafe fn _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0()
-> f64 {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: f64 = 0.0;
    v___x_3243_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3244_ = lean_float_of_nat(v___x_3243_);
    return v___x_3244_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0(
    mut v_x_3245_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___x_3246_: f64 = 0.0;
    v___x_3246_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0_once), _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___closed__0);
    return v___x_3246_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0___boxed(
    mut v_x_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3248_: f64 = 0.0;
    let mut v_r_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3248_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___lam__0(v_x_3247_);
    crate::leanh::lean_dec(v_x_3247_);
    v_r_3249_ = crate::leanh::lean_box_float(v_res_3248_);
    return v_r_3249_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore(
    mut v_relevant_3251_: *mut crate::leanh::LeanObject,
    mut v_candidate_3252_: *mut crate::leanh::LeanObject,
) -> f64 {
    let mut v___f_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: f64 = 0.0;
    v___f_3253_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___closed__0;
    v___x_3254_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore(
            v___f_3253_,
            v_relevant_3251_,
            v_candidate_3252_,
        );
    return v___x_3254_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore___boxed(
    mut v_relevant_3255_: *mut crate::leanh::LeanObject,
    mut v_candidate_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3257_: f64 = 0.0;
    let mut v_r_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3257_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_unweightedScore(
            v_relevant_3255_,
            v_candidate_3256_,
        );
    v_r_3258_ = crate::leanh::lean_box_float(v_res_3257_);
    return v_r_3258_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0(
    mut v_accept_3259_: *mut crate::leanh::LeanObject,
    mut v_x_3260_: *mut crate::leanh::LeanObject,
    mut v_y_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v_a_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut v_a_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3264_);
                crate::leanh::lean_inc_ref(v___y_3263_);
                crate::leanh::lean_inc_ref(v_y_3261_);
                v___x_3266_ = crate::leanh::lean_apply_4(
                    v_accept_3259_,
                    v_y_3261_,
                    v___y_3263_,
                    v___y_3264_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3266_) == 0 {
                    v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                    v_isSharedCheck_3284_ = (!crate::leanh::lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v___x_3269_ = v___x_3266_;
                        v_isShared_3270_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3267_);
                        crate::leanh::lean_dec(v___x_3266_);
                        v___x_3269_ = crate::leanh::lean_box(0);
                        v_isShared_3270_ = v_isSharedCheck_3284_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3262_);
                    crate::leanh::lean_dec_ref(v_y_3261_);
                    crate::leanh::lean_dec(v_x_3260_);
                    v_a_3285_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                    v_isSharedCheck_3292_ = (!crate::leanh::lean_is_exclusive(v___x_3266_)) as u8;
                    if v_isSharedCheck_3292_ == 0 {
                        v___x_3287_ = v___x_3266_;
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3285_);
                        crate::leanh::lean_dec(v___x_3266_);
                        v___x_3287_ = crate::leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3279_ = (crate::leanh::lean_unbox(v_a_3267_) as u8);
                crate::leanh::lean_dec(v_a_3267_);
                if v___x_3279_ == 0 {
                    crate::leanh::lean_dec_ref(v_y_3261_);
                    crate::leanh::lean_dec(v_x_3260_);
                    v_a_3272_ = v___y_3262_;
                    state = 2;
                    continue;
                } else {
                    v___x_3280_ = l_Lean_ConstantInfo_type(v_y_3261_);
                    crate::leanh::lean_dec_ref(v_y_3261_);
                    v___x_3281_ = l_Lean_Expr_getUsedConstantsAsSet(v___x_3280_);
                    v___x_3282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v_x_3260_);
                    crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3281_);
                    v___x_3283_ = lean_array_push(v___y_3262_, v___x_3282_);
                    v_a_3272_ = v___x_3283_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3273_ = crate::leanh::lean_box(0);
                v___x_3274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3274_, 0, v___x_3273_);
                crate::leanh::lean_ctor_set(v___x_3274_, 1, v_a_3272_);
                v___x_3275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3274_);
                if v_isShared_3270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3275_);
                    v___x_3277_ = v___x_3269_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
                    v___x_3277_ = v_reuseFailAlloc_3278_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3277_;
            }
            4 => {
                if v_isShared_3288_ == 0 {
                    v___x_3290_ = v___x_3287_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0___boxed(
    mut v_accept_3293_: *mut crate::leanh::LeanObject,
    mut v_x_3294_: *mut crate::leanh::LeanObject,
    mut v_y_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3300_ =
        l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0(
            v_accept_3293_,
            v_x_3294_,
            v_y_3295_,
            v___y_3296_,
            v___y_3297_,
            v___y_3298_,
        );
    crate::leanh::lean_dec(v___y_3298_);
    crate::leanh::lean_dec_ref(v___y_3297_);
    return v_res_3300_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3301_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__0);
    v___x_3303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3303_, 0, v___x_3302_);
    return v___x_3303_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3304_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1);
    v___x_3305_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3306_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3306_, 0, v___x_3305_);
    crate::leanh::lean_ctor_set(v___x_3306_, 1, v___x_3305_);
    crate::leanh::lean_ctor_set(v___x_3306_, 2, v___x_3305_);
    crate::leanh::lean_ctor_set(v___x_3306_, 3, v___x_3305_);
    crate::leanh::lean_ctor_set(v___x_3306_, 4, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 5, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 6, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 7, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 8, v___x_3304_);
    crate::leanh::lean_ctor_set(v___x_3306_, 9, v___x_3304_);
    return v___x_3306_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3308_ = lean_mk_empty_array_with_capacity(v___x_3307_);
    v___x_3309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3308_);
    return v___x_3309_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: usize = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = 5usize;
    v___x_3311_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3312_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3313_ = lean_mk_empty_array_with_capacity(v___x_3312_);
    v___x_3314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__3);
    v___x_3315_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3315_, 0, v___x_3314_);
    crate::leanh::lean_ctor_set(v___x_3315_, 1, v___x_3313_);
    crate::leanh::lean_ctor_set(v___x_3315_, 2, v___x_3311_);
    crate::leanh::lean_ctor_set(v___x_3315_, 3, v___x_3311_);
    crate::leanh::lean_ctor_set_usize(v___x_3315_, 4, v___x_3310_);
    return v___x_3315_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3316_ = crate::leanh::lean_box(1);
    v___x_3317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__4);
    v___x_3318_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__1);
    v___x_3319_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3319_, 0, v___x_3318_);
    crate::leanh::lean_ctor_set(v___x_3319_, 1, v___x_3317_);
    crate::leanh::lean_ctor_set(v___x_3319_, 2, v___x_3316_);
    return v___x_3319_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13(
    mut v_msgData_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = lean_st_ref_get(v___y_3322_);
    v_env_3325_ = crate::leanh::lean_ctor_get(v___x_3324_, 0);
    crate::leanh::lean_inc_ref(v_env_3325_);
    crate::leanh::lean_dec(v___x_3324_);
    v_options_3326_ = crate::leanh::lean_ctor_get(v___y_3321_, 2);
    v___x_3327_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__2);
    v___x_3328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___closed__5);
    crate::leanh::lean_inc_ref(v_options_3326_);
    v___x_3329_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3329_, 0, v_env_3325_);
    crate::leanh::lean_ctor_set(v___x_3329_, 1, v___x_3327_);
    crate::leanh::lean_ctor_set(v___x_3329_, 2, v___x_3328_);
    crate::leanh::lean_ctor_set(v___x_3329_, 3, v_options_3326_);
    v___x_3330_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3330_, 0, v___x_3329_);
    crate::leanh::lean_ctor_set(v___x_3330_, 1, v_msgData_3320_);
    v___x_3331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3331_, 0, v___x_3330_);
    return v___x_3331_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13___boxed(
    mut v_msgData_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13(v_msgData_3332_, v___y_3333_, v___y_3334_);
    crate::leanh::lean_dec(v___y_3334_);
    crate::leanh::lean_dec_ref(v___y_3333_);
    return v_res_3336_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(
    mut v_cls_3340_: *mut crate::leanh::LeanObject,
    mut v_msg_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_tid_3364_: u64 = 0;
    let mut v_traces_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: f64 = 0.0;
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3345_ = crate::leanh::lean_ctor_get(v___y_3342_, 5);
                v___x_3346_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9_spec__13(v_msg_3341_, v___y_3342_, v___y_3343_);
                v_a_3347_ = crate::leanh::lean_ctor_get(v___x_3346_, 0);
                v_isSharedCheck_3391_ = (!crate::leanh::lean_is_exclusive(v___x_3346_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v___x_3349_ = v___x_3346_;
                    v_isShared_3350_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3347_);
                    crate::leanh::lean_dec(v___x_3346_);
                    v___x_3349_ = crate::leanh::lean_box(0);
                    v_isShared_3350_ = v_isSharedCheck_3391_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3351_ = lean_st_ref_take(v___y_3343_);
                v_traceState_3352_ = crate::leanh::lean_ctor_get(v___x_3351_, 4);
                v_env_3353_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                v_nextMacroScope_3354_ = crate::leanh::lean_ctor_get(v___x_3351_, 1);
                v_ngen_3355_ = crate::leanh::lean_ctor_get(v___x_3351_, 2);
                v_auxDeclNGen_3356_ = crate::leanh::lean_ctor_get(v___x_3351_, 3);
                v_cache_3357_ = crate::leanh::lean_ctor_get(v___x_3351_, 5);
                v_messages_3358_ = crate::leanh::lean_ctor_get(v___x_3351_, 6);
                v_infoState_3359_ = crate::leanh::lean_ctor_get(v___x_3351_, 7);
                v_snapshotTasks_3360_ = crate::leanh::lean_ctor_get(v___x_3351_, 8);
                v_isSharedCheck_3390_ = (!crate::leanh::lean_is_exclusive(v___x_3351_)) as u8;
                if v_isSharedCheck_3390_ == 0 {
                    v___x_3362_ = v___x_3351_;
                    v_isShared_3363_ = v_isSharedCheck_3390_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3360_);
                    crate::leanh::lean_inc(v_infoState_3359_);
                    crate::leanh::lean_inc(v_messages_3358_);
                    crate::leanh::lean_inc(v_cache_3357_);
                    crate::leanh::lean_inc(v_traceState_3352_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3356_);
                    crate::leanh::lean_inc(v_ngen_3355_);
                    crate::leanh::lean_inc(v_nextMacroScope_3354_);
                    crate::leanh::lean_inc(v_env_3353_);
                    crate::leanh::lean_dec(v___x_3351_);
                    v___x_3362_ = crate::leanh::lean_box(0);
                    v_isShared_3363_ = v_isSharedCheck_3390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3364_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3352_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3365_ = crate::leanh::lean_ctor_get(v_traceState_3352_, 0);
                v_isSharedCheck_3389_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3352_)) as u8;
                if v_isSharedCheck_3389_ == 0 {
                    v___x_3367_ = v_traceState_3352_;
                    v_isShared_3368_ = v_isSharedCheck_3389_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3365_);
                    crate::leanh::lean_dec(v_traceState_3352_);
                    v___x_3367_ = crate::leanh::lean_box(0);
                    v_isShared_3368_ = v_isSharedCheck_3389_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3369_ = crate::leanh::lean_box(0);
                v___x_3370_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0_once), _init_l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_weightedScore___closed__0);
                v___x_3371_ = 0;
                v___x_3372_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__0;
                v___x_3373_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3373_, 0, v_cls_3340_);
                crate::leanh::lean_ctor_set(v___x_3373_, 1, v___x_3369_);
                crate::leanh::lean_ctor_set(v___x_3373_, 2, v___x_3372_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3370_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3370_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3371_,
                );
                v___x_3374_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___closed__1;
                v___x_3375_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3373_);
                crate::leanh::lean_ctor_set(v___x_3375_, 1, v_a_3347_);
                crate::leanh::lean_ctor_set(v___x_3375_, 2, v___x_3374_);
                crate::leanh::lean_inc(v_ref_3345_);
                v___x_3376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3376_, 0, v_ref_3345_);
                crate::leanh::lean_ctor_set(v___x_3376_, 1, v___x_3375_);
                v___x_3377_ = l_Lean_PersistentArray_push___redArg(v_traces_3365_, v___x_3376_);
                if v_isShared_3368_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3377_);
                    v___x_3379_ = v___x_3367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3377_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3388_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3364_,
                    );
                    v___x_3379_ = v_reuseFailAlloc_3388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3362_, 4, v___x_3379_);
                    v___x_3381_ = v___x_3362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3387_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_env_3353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_nextMacroScope_3354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 2, v_ngen_3355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 3, v_auxDeclNGen_3356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 4, v___x_3379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 5, v_cache_3357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 6, v_messages_3358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 7, v_infoState_3359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3387_, 8, v_snapshotTasks_3360_);
                    v___x_3381_ = v_reuseFailAlloc_3387_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3382_ = lean_st_ref_set(v___y_3343_, v___x_3381_);
                v___x_3383_ = crate::leanh::lean_box(0);
                if v_isShared_3350_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3349_, 0, v___x_3383_);
                    v___x_3385_ = v___x_3349_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
                    v___x_3385_ = v_reuseFailAlloc_3386_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9___boxed(
    mut v_cls_3392_: *mut crate::leanh::LeanObject,
    mut v_msg_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v_cls_3392_, v_msg_3393_, v___y_3394_, v___y_3395_);
    crate::leanh::lean_dec(v___y_3395_);
    crate::leanh::lean_dec_ref(v___y_3394_);
    return v_res_3397_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(
    mut v_sz_3398_: usize,
    mut v_i_3399_: usize,
    mut v_bs_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: u8 = 0;
    let mut v_v_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3408_: u8 = 0;
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: usize = 0;
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut v_unused_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3401_ = lean_usize_dec_lt(v_i_3399_, v_sz_3398_);
                if v___x_3401_ == 0 {
                    return v_bs_3400_;
                } else {
                    v_v_3402_ = lean_array_uget_borrowed(v_bs_3400_, v_i_3399_);
                    v_snd_3403_ = crate::leanh::lean_ctor_get(v_v_3402_, 1);
                    crate::leanh::lean_inc(v_snd_3403_);
                    v_fst_3404_ = crate::leanh::lean_ctor_get(v_v_3402_, 0);
                    crate::leanh::lean_inc(v_fst_3404_);
                    v_snd_3405_ = crate::leanh::lean_ctor_get(v_snd_3403_, 1);
                    v_isSharedCheck_3418_ = (!crate::leanh::lean_is_exclusive(v_snd_3403_)) as u8;
                    if v_isSharedCheck_3418_ == 0 {
                        v_unused_3419_ = crate::leanh::lean_ctor_get(v_snd_3403_, 0);
                        crate::leanh::lean_dec(v_unused_3419_);
                        v___x_3407_ = v_snd_3403_;
                        v_isShared_3408_ = v_isSharedCheck_3418_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3405_);
                        crate::leanh::lean_dec(v_snd_3403_);
                        v___x_3407_ = crate::leanh::lean_box(0);
                        v_isShared_3408_ = v_isSharedCheck_3418_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3409_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3410_ = lean_array_uset(v_bs_3400_, v_i_3399_, v___x_3409_);
                if v_isShared_3408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3407_, 0, v_fst_3404_);
                    v___x_3412_ = v___x_3407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_fst_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_snd_3405_);
                    v___x_3412_ = v_reuseFailAlloc_3417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3413_ = 1usize;
                v___x_3414_ = lean_usize_add(v_i_3399_, v___x_3413_);
                v___x_3415_ = lean_array_uset(v_bs_x27_3410_, v_i_3399_, v___x_3412_);
                v_i_3399_ = v___x_3414_;
                v_bs_3400_ = v___x_3415_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7___boxed(
    mut v_sz_3420_: *mut crate::leanh::LeanObject,
    mut v_i_3421_: *mut crate::leanh::LeanObject,
    mut v_bs_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3423_: usize = 0;
    let mut v_i_boxed_3424_: usize = 0;
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3423_ = crate::leanh::lean_unbox_usize(v_sz_3420_);
    crate::leanh::lean_dec(v_sz_3420_);
    v_i_boxed_3424_ = crate::leanh::lean_unbox_usize(v_i_3421_);
    crate::leanh::lean_dec(v_i_3421_);
    v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(v_sz_boxed_3423_, v_i_boxed_3424_, v_bs_3422_);
    return v_res_3425_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(
    mut v___x_3426_: f64,
    mut v_as_3427_: *mut crate::leanh::LeanObject,
    mut v_sz_3428_: usize,
    mut v_i_3429_: usize,
    mut v_b_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: usize = 0;
    let mut v___x_3434_: usize = 0;
    let mut v___x_3436_: u8 = 0;
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v___x_3445_: f64 = 0.0;
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ = lean_usize_dec_lt(v_i_3429_, v_sz_3428_);
                if v___x_3436_ == 0 {
                    return v_b_3430_;
                } else {
                    v_a_3437_ = lean_array_uget_borrowed(v_as_3427_, v_i_3429_);
                    v_snd_3438_ = crate::leanh::lean_ctor_get(v_a_3437_, 1);
                    v_snd_3439_ = crate::leanh::lean_ctor_get(v_snd_3438_, 1);
                    v_fst_3440_ = crate::leanh::lean_ctor_get(v_b_3430_, 0);
                    v_snd_3441_ = crate::leanh::lean_ctor_get(v_b_3430_, 1);
                    v_isSharedCheck_3455_ = (!crate::leanh::lean_is_exclusive(v_b_3430_)) as u8;
                    if v_isSharedCheck_3455_ == 0 {
                        v___x_3443_ = v_b_3430_;
                        v_isShared_3444_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3441_);
                        crate::leanh::lean_inc(v_fst_3440_);
                        crate::leanh::lean_dec(v_b_3430_);
                        v___x_3443_ = crate::leanh::lean_box(0);
                        v_isShared_3444_ = v_isSharedCheck_3455_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3433_ = 1usize;
                v___x_3434_ = lean_usize_add(v_i_3429_, v___x_3433_);
                v_i_3429_ = v___x_3434_;
                v_b_3430_ = v_a_3432_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3445_ = crate::leanh::lean_unbox_float(v_snd_3439_);
                v___x_3446_ = lean_float_decLe(v___x_3426_, v___x_3445_);
                if v___x_3446_ == 0 {
                    crate::leanh::lean_inc(v_a_3437_);
                    v___x_3447_ = lean_array_push(v_snd_3441_, v_a_3437_);
                    if v_isShared_3444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3443_, 1, v___x_3447_);
                        v___x_3449_ = v___x_3443_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_fst_3440_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3447_);
                        v___x_3449_ = v_reuseFailAlloc_3450_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_a_3437_);
                    v___x_3451_ = lean_array_push(v_fst_3440_, v_a_3437_);
                    if v_isShared_3444_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3443_, 0, v___x_3451_);
                        v___x_3453_ = v___x_3443_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_snd_3441_);
                        v___x_3453_ = v_reuseFailAlloc_3454_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_3432_ = v___x_3449_;
                state = 1;
                continue;
            }
            4 => {
                v_a_3432_ = v___x_3453_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2___boxed(
    mut v___x_3456_: *mut crate::leanh::LeanObject,
    mut v_as_3457_: *mut crate::leanh::LeanObject,
    mut v_sz_3458_: *mut crate::leanh::LeanObject,
    mut v_i_3459_: *mut crate::leanh::LeanObject,
    mut v_b_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_17435__boxed_3461_: f64 = 0.0;
    let mut v_sz_boxed_3462_: usize = 0;
    let mut v_i_boxed_3463_: usize = 0;
    let mut v_res_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_17435__boxed_3461_ = crate::leanh::lean_unbox_float(v___x_3456_);
    crate::leanh::lean_dec_ref(v___x_3456_);
    v_sz_boxed_3462_ = crate::leanh::lean_unbox_usize(v_sz_3458_);
    crate::leanh::lean_dec(v_sz_3458_);
    v_i_boxed_3463_ = crate::leanh::lean_unbox_usize(v_i_3459_);
    crate::leanh::lean_dec(v_i_3459_);
    v_res_3464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(v___x_17435__boxed_3461_, v_as_3457_, v_sz_boxed_3462_, v_i_boxed_3463_, v_b_3460_);
    crate::leanh::lean_dec_ref(v_as_3457_);
    return v_res_3464_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__11(
    mut v_a_3465_: *mut crate::leanh::LeanObject,
    mut v_a_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3465_) == 0 {
                    v___x_3467_ = l_List_reverse___redArg(v_a_3466_);
                    return v___x_3467_;
                } else {
                    v_head_3468_ = crate::leanh::lean_ctor_get(v_a_3465_, 0);
                    v_tail_3469_ = crate::leanh::lean_ctor_get(v_a_3465_, 1);
                    v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v_a_3465_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v___x_3471_ = v_a_3465_;
                        v_isShared_3472_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3469_);
                        crate::leanh::lean_inc(v_head_3468_);
                        crate::leanh::lean_dec(v_a_3465_);
                        v___x_3471_ = crate::leanh::lean_box(0);
                        v_isShared_3472_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3473_ = l_Lean_MessageData_ofName(v_head_3468_);
                if v_isShared_3472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3471_, 1, v_a_3466_);
                    crate::leanh::lean_ctor_set(v___x_3471_, 0, v___x_3473_);
                    v___x_3475_ = v___x_3471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_a_3466_);
                    v___x_3475_ = v_reuseFailAlloc_3477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3465_ = v_tail_3469_;
                v_a_3466_ = v___x_3475_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(
    mut v_as_3479_: *mut crate::leanh::LeanObject,
    mut v_i_3480_: usize,
    mut v_stop_3481_: usize,
    mut v_b_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3483_: u8 = 0;
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: f64 = 0.0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3483_ = lean_usize_dec_eq(v_i_3480_, v_stop_3481_);
                if v___x_3483_ == 0 {
                    v___x_3484_ = lean_array_uget_borrowed(v_as_3479_, v_i_3480_);
                    v_snd_3485_ = crate::leanh::lean_ctor_get(v___x_3484_, 1);
                    v_fst_3486_ = crate::leanh::lean_ctor_get(v___x_3484_, 0);
                    v_snd_3487_ = crate::leanh::lean_ctor_get(v_snd_3485_, 1);
                    v___x_3488_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_3486_);
                    v___x_3489_ = crate::leanh::lean_alloc_ctor(0, 2, (8) as u32);
                    crate::leanh::lean_ctor_set(v___x_3489_, 0, v_fst_3486_);
                    crate::leanh::lean_ctor_set(v___x_3489_, 1, v___x_3488_);
                    v___x_3490_ = crate::leanh::lean_unbox_float(v_snd_3487_);
                    crate::leanh::lean_ctor_set_float(
                        v___x_3489_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_3490_,
                    );
                    v___x_3491_ = lean_array_push(v_b_3482_, v___x_3489_);
                    v___x_3492_ = 1usize;
                    v___x_3493_ = lean_usize_add(v_i_3480_, v___x_3492_);
                    v_i_3480_ = v___x_3493_;
                    v_b_3482_ = v___x_3491_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3482_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5___boxed(
    mut v_as_3495_: *mut crate::leanh::LeanObject,
    mut v_i_3496_: *mut crate::leanh::LeanObject,
    mut v_stop_3497_: *mut crate::leanh::LeanObject,
    mut v_b_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3499_: usize = 0;
    let mut v_stop_boxed_3500_: usize = 0;
    let mut v_res_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3499_ = crate::leanh::lean_unbox_usize(v_i_3496_);
    crate::leanh::lean_dec(v_i_3496_);
    v_stop_boxed_3500_ = crate::leanh::lean_unbox_usize(v_stop_3497_);
    crate::leanh::lean_dec(v_stop_3497_);
    v_res_3501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v_as_3495_, v_i_boxed_3499_, v_stop_boxed_3500_, v_b_3498_);
    crate::leanh::lean_dec_ref(v_as_3495_);
    return v_res_3501_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(
    mut v_sz_3502_: usize,
    mut v_i_3503_: usize,
    mut v_bs_3504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3505_: u8 = 0;
    let mut v_v_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3512_: u8 = 0;
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: usize = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_unused_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = lean_usize_dec_lt(v_i_3503_, v_sz_3502_);
                if v___x_3505_ == 0 {
                    return v_bs_3504_;
                } else {
                    v_v_3506_ = lean_array_uget_borrowed(v_bs_3504_, v_i_3503_);
                    v_snd_3507_ = crate::leanh::lean_ctor_get(v_v_3506_, 1);
                    crate::leanh::lean_inc(v_snd_3507_);
                    v_fst_3508_ = crate::leanh::lean_ctor_get(v_v_3506_, 0);
                    crate::leanh::lean_inc(v_fst_3508_);
                    v_fst_3509_ = crate::leanh::lean_ctor_get(v_snd_3507_, 0);
                    v_isSharedCheck_3522_ = (!crate::leanh::lean_is_exclusive(v_snd_3507_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v_unused_3523_ = crate::leanh::lean_ctor_get(v_snd_3507_, 1);
                        crate::leanh::lean_dec(v_unused_3523_);
                        v___x_3511_ = v_snd_3507_;
                        v_isShared_3512_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3509_);
                        crate::leanh::lean_dec(v_snd_3507_);
                        v___x_3511_ = crate::leanh::lean_box(0);
                        v_isShared_3512_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3513_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3514_ = lean_array_uset(v_bs_3504_, v_i_3503_, v___x_3513_);
                if v_isShared_3512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3511_, 1, v_fst_3509_);
                    crate::leanh::lean_ctor_set(v___x_3511_, 0, v_fst_3508_);
                    v___x_3516_ = v___x_3511_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_fst_3508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_fst_3509_);
                    v___x_3516_ = v_reuseFailAlloc_3521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3517_ = 1usize;
                v___x_3518_ = lean_usize_add(v_i_3503_, v___x_3517_);
                v___x_3519_ = lean_array_uset(v_bs_x27_3514_, v_i_3503_, v___x_3516_);
                v_i_3503_ = v___x_3518_;
                v_bs_3504_ = v___x_3519_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3___boxed(
    mut v_sz_3524_: *mut crate::leanh::LeanObject,
    mut v_i_3525_: *mut crate::leanh::LeanObject,
    mut v_bs_3526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3527_: usize = 0;
    let mut v_i_boxed_3528_: usize = 0;
    let mut v_res_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3527_ = crate::leanh::lean_unbox_usize(v_sz_3524_);
    crate::leanh::lean_dec(v_sz_3524_);
    v_i_boxed_3528_ = crate::leanh::lean_unbox_usize(v_i_3525_);
    crate::leanh::lean_dec(v_i_3525_);
    v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(v_sz_boxed_3527_, v_i_boxed_3528_, v_bs_3526_);
    return v_res_3529_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(
    mut v_init_3530_: *mut crate::leanh::LeanObject,
    mut v_x_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3531_) == 0 {
                    v_k_3532_ = crate::leanh::lean_ctor_get(v_x_3531_, 1);
                    v_l_3533_ = crate::leanh::lean_ctor_get(v_x_3531_, 3);
                    v_r_3534_ = crate::leanh::lean_ctor_get(v_x_3531_, 4);
                    v___x_3535_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v_init_3530_, v_r_3534_);
                    crate::leanh::lean_inc(v_k_3532_);
                    v___x_3536_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3536_, 0, v_k_3532_);
                    crate::leanh::lean_ctor_set(v___x_3536_, 1, v___x_3535_);
                    v_init_3530_ = v___x_3536_;
                    v_x_3531_ = v_l_3533_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3530_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10___boxed(
    mut v_init_3538_: *mut crate::leanh::LeanObject,
    mut v_x_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3540_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v_init_3538_, v_x_3539_);
    crate::leanh::lean_dec(v_x_3539_);
    return v_res_3540_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___redArg(
    mut v_hi_3541_: *mut crate::leanh::LeanObject,
    mut v_pivot_3542_: *mut crate::leanh::LeanObject,
    mut v_as_3543_: *mut crate::leanh::LeanObject,
    mut v_i_3544_: *mut crate::leanh::LeanObject,
    mut v_k_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: f64 = 0.0;
    let mut v___x_3555_: f64 = 0.0;
    let mut v___x_3556_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3546_ = lean_nat_dec_lt(v_k_3545_, v_hi_3541_);
                if v___x_3546_ == 0 {
                    crate::leanh::lean_dec(v_k_3545_);
                    v___x_3547_ = lean_array_fswap(v_as_3543_, v_i_3544_, v_hi_3541_);
                    v___x_3548_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3548_, 0, v_i_3544_);
                    crate::leanh::lean_ctor_set(v___x_3548_, 1, v___x_3547_);
                    return v___x_3548_;
                } else {
                    v___x_3549_ = lean_array_fget_borrowed(v_as_3543_, v_k_3545_);
                    v_snd_3550_ = crate::leanh::lean_ctor_get(v___x_3549_, 1);
                    v_snd_3551_ = crate::leanh::lean_ctor_get(v_pivot_3542_, 1);
                    v_snd_3552_ = crate::leanh::lean_ctor_get(v_snd_3550_, 1);
                    v_snd_3553_ = crate::leanh::lean_ctor_get(v_snd_3551_, 1);
                    v___x_3554_ = crate::leanh::lean_unbox_float(v_snd_3553_);
                    v___x_3555_ = crate::leanh::lean_unbox_float(v_snd_3552_);
                    v___x_3556_ = lean_float_decLt(v___x_3554_, v___x_3555_);
                    if v___x_3556_ == 0 {
                        v___x_3557_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3558_ = lean_nat_add(v_k_3545_, v___x_3557_);
                        crate::leanh::lean_dec(v_k_3545_);
                        v_k_3545_ = v___x_3558_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3560_ = lean_array_fswap(v_as_3543_, v_i_3544_, v_k_3545_);
                        v___x_3561_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3562_ = lean_nat_add(v_i_3544_, v___x_3561_);
                        crate::leanh::lean_dec(v_i_3544_);
                        v___x_3563_ = lean_nat_add(v_k_3545_, v___x_3561_);
                        crate::leanh::lean_dec(v_k_3545_);
                        v_as_3543_ = v___x_3560_;
                        v_i_3544_ = v___x_3562_;
                        v_k_3545_ = v___x_3563_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___redArg___boxed(
    mut v_hi_3565_: *mut crate::leanh::LeanObject,
    mut v_pivot_3566_: *mut crate::leanh::LeanObject,
    mut v_as_3567_: *mut crate::leanh::LeanObject,
    mut v_i_3568_: *mut crate::leanh::LeanObject,
    mut v_k_3569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___redArg(v_hi_3565_, v_pivot_3566_, v_as_3567_, v_i_3568_, v_k_3569_);
    crate::leanh::lean_dec_ref(v_pivot_3566_);
    crate::leanh::lean_dec(v_hi_3565_);
    return v_res_3570_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(
    mut v_x_3571_: *mut crate::leanh::LeanObject,
    mut v_x_3572_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: f64 = 0.0;
    let mut v___x_3578_: f64 = 0.0;
    let mut v___x_3579_: u8 = 0;
    v_snd_3573_ = crate::leanh::lean_ctor_get(v_x_3571_, 1);
    v_snd_3574_ = crate::leanh::lean_ctor_get(v_x_3572_, 1);
    v_snd_3575_ = crate::leanh::lean_ctor_get(v_snd_3573_, 1);
    v_snd_3576_ = crate::leanh::lean_ctor_get(v_snd_3574_, 1);
    v___x_3577_ = crate::leanh::lean_unbox_float(v_snd_3576_);
    v___x_3578_ = crate::leanh::lean_unbox_float(v_snd_3575_);
    v___x_3579_ = lean_float_decLt(v___x_3577_, v___x_3578_);
    return v___x_3579_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0___boxed(
    mut v_x_3580_: *mut crate::leanh::LeanObject,
    mut v_x_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3582_: u8 = 0;
    let mut v_r_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v_x_3580_, v_x_3581_);
    crate::leanh::lean_dec_ref(v_x_3581_);
    crate::leanh::lean_dec_ref(v_x_3580_);
    v_r_3583_ = crate::leanh::lean_box((v_res_3582_) as usize);
    return v_r_3583_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(
    mut v_n_3584_: *mut crate::leanh::LeanObject,
    mut v_as_3585_: *mut crate::leanh::LeanObject,
    mut v_lo_3586_: *mut crate::leanh::LeanObject,
    mut v_hi_3587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3599_ = lean_nat_dec_lt(v_lo_3586_, v_hi_3587_);
                if v___x_3599_ == 0 {
                    crate::leanh::lean_dec(v_lo_3586_);
                    return v_as_3585_;
                } else {
                    v___x_3600_ = lean_nat_add(v_lo_3586_, v_hi_3587_);
                    v___x_3601_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3602_ = lean_nat_shiftr(v___x_3600_, v___x_3601_);
                    crate::leanh::lean_dec(v___x_3600_);
                    v___x_3615_ = lean_array_fget_borrowed(v_as_3585_, v_mid_3602_);
                    v___x_3616_ = lean_array_fget_borrowed(v_as_3585_, v_lo_3586_);
                    v___x_3617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_3615_, v___x_3616_);
                    if v___x_3617_ == 0 {
                        v___y_3610_ = v_as_3585_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3618_ = lean_array_fswap(v_as_3585_, v_lo_3586_, v_mid_3602_);
                        v___y_3610_ = v___x_3618_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3590_ = lean_array_fget(v___y_3589_, v_hi_3587_);
                crate::leanh::lean_inc_n(v_lo_3586_, 2);
                v___x_3591_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___redArg(v_hi_3587_, v_pivot_3590_, v___y_3589_, v_lo_3586_, v_lo_3586_);
                crate::leanh::lean_dec(v_pivot_3590_);
                v_fst_3592_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                crate::leanh::lean_inc(v_fst_3592_);
                v_snd_3593_ = crate::leanh::lean_ctor_get(v___x_3591_, 1);
                crate::leanh::lean_inc(v_snd_3593_);
                crate::leanh::lean_dec_ref(v___x_3591_);
                v___x_3594_ = lean_nat_dec_le(v_hi_3587_, v_fst_3592_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_3584_, v_snd_3593_, v_lo_3586_, v_fst_3592_);
                    v___x_3596_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3597_ = lean_nat_add(v_fst_3592_, v___x_3596_);
                    crate::leanh::lean_dec(v_fst_3592_);
                    v_as_3585_ = v___x_3595_;
                    v_lo_3586_ = v___x_3597_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3592_);
                    crate::leanh::lean_dec(v_lo_3586_);
                    return v_snd_3593_;
                }
            }
            2 => {
                v___x_3605_ = lean_array_fget_borrowed(v___y_3604_, v_mid_3602_);
                v___x_3606_ = lean_array_fget_borrowed(v___y_3604_, v_hi_3587_);
                v___x_3607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_3605_, v___x_3606_);
                if v___x_3607_ == 0 {
                    crate::leanh::lean_dec(v_mid_3602_);
                    v___y_3589_ = v___y_3604_;
                    state = 1;
                    continue;
                } else {
                    v___x_3608_ = lean_array_fswap(v___y_3604_, v_mid_3602_, v_hi_3587_);
                    crate::leanh::lean_dec(v_mid_3602_);
                    v___y_3589_ = v___x_3608_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3611_ = lean_array_fget_borrowed(v___y_3610_, v_hi_3587_);
                v___x_3612_ = lean_array_fget_borrowed(v___y_3610_, v_lo_3586_);
                v___x_3613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___lam__0(v___x_3611_, v___x_3612_);
                if v___x_3613_ == 0 {
                    v___y_3604_ = v___y_3610_;
                    state = 2;
                    continue;
                } else {
                    v___x_3614_ = lean_array_fswap(v___y_3610_, v_lo_3586_, v_hi_3587_);
                    v___y_3604_ = v___x_3614_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg___boxed(
    mut v_n_3619_: *mut crate::leanh::LeanObject,
    mut v_as_3620_: *mut crate::leanh::LeanObject,
    mut v_lo_3621_: *mut crate::leanh::LeanObject,
    mut v_hi_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_3619_, v_as_3620_, v_lo_3621_, v_hi_3622_);
    crate::leanh::lean_dec(v_hi_3622_);
    crate::leanh::lean_dec(v_n_3619_);
    return v_res_3623_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(
    mut v_score_3624_: *mut crate::leanh::LeanObject,
    mut v___x_3625_: *mut crate::leanh::LeanObject,
    mut v_sz_3626_: usize,
    mut v_i_3627_: usize,
    mut v_bs_3628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3629_: u8 = 0;
    let mut v_v_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: usize = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3629_ = lean_usize_dec_lt(v_i_3627_, v_sz_3626_);
                if v___x_3629_ == 0 {
                    crate::leanh::lean_dec(v___x_3625_);
                    crate::leanh::lean_dec_ref(v_score_3624_);
                    return v_bs_3628_;
                } else {
                    v_v_3630_ = lean_array_uget(v_bs_3628_, v_i_3627_);
                    v_fst_3631_ = crate::leanh::lean_ctor_get(v_v_3630_, 0);
                    v_snd_3632_ = crate::leanh::lean_ctor_get(v_v_3630_, 1);
                    v_isSharedCheck_3647_ = (!crate::leanh::lean_is_exclusive(v_v_3630_)) as u8;
                    if v_isSharedCheck_3647_ == 0 {
                        v___x_3634_ = v_v_3630_;
                        v_isShared_3635_ = v_isSharedCheck_3647_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3632_);
                        crate::leanh::lean_inc(v_fst_3631_);
                        crate::leanh::lean_dec(v_v_3630_);
                        v___x_3634_ = crate::leanh::lean_box(0);
                        v_isShared_3635_ = v_isSharedCheck_3647_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3636_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_3637_ = lean_array_uset(v_bs_3628_, v_i_3627_, v___x_3636_);
                crate::leanh::lean_inc_ref(v_score_3624_);
                crate::leanh::lean_inc(v_snd_3632_);
                crate::leanh::lean_inc(v___x_3625_);
                v___x_3638_ = crate::leanh::lean_apply_2(v_score_3624_, v___x_3625_, v_snd_3632_);
                if v_isShared_3635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3634_, 1, v___x_3638_);
                    crate::leanh::lean_ctor_set(v___x_3634_, 0, v_snd_3632_);
                    v___x_3640_ = v___x_3634_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_snd_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 1, v___x_3638_);
                    v___x_3640_ = v_reuseFailAlloc_3646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3641_, 0, v_fst_3631_);
                crate::leanh::lean_ctor_set(v___x_3641_, 1, v___x_3640_);
                v___x_3642_ = 1usize;
                v___x_3643_ = lean_usize_add(v_i_3627_, v___x_3642_);
                v___x_3644_ = lean_array_uset(v_bs_x27_3637_, v_i_3627_, v___x_3641_);
                v_i_3627_ = v___x_3643_;
                v_bs_3628_ = v___x_3644_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1___boxed(
    mut v_score_3648_: *mut crate::leanh::LeanObject,
    mut v___x_3649_: *mut crate::leanh::LeanObject,
    mut v_sz_3650_: *mut crate::leanh::LeanObject,
    mut v_i_3651_: *mut crate::leanh::LeanObject,
    mut v_bs_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3653_: usize = 0;
    let mut v_i_boxed_3654_: usize = 0;
    let mut v_res_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3653_ = crate::leanh::lean_unbox_usize(v_sz_3650_);
    crate::leanh::lean_dec(v_sz_3650_);
    v_i_boxed_3654_ = crate::leanh::lean_unbox_usize(v_i_3651_);
    crate::leanh::lean_dec(v_i_3651_);
    v_res_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(v_score_3648_, v___x_3649_, v_sz_boxed_3653_, v_i_boxed_3654_, v_bs_3652_);
    return v_res_3655_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(
    mut v_as_3656_: *mut crate::leanh::LeanObject,
    mut v_i_3657_: usize,
    mut v_stop_3658_: usize,
    mut v_b_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3660_ = lean_usize_dec_eq(v_i_3657_, v_stop_3658_);
                if v___x_3660_ == 0 {
                    v___x_3661_ = lean_array_uget_borrowed(v_as_3656_, v_i_3657_);
                    v_snd_3662_ = crate::leanh::lean_ctor_get(v___x_3661_, 1);
                    v_fst_3663_ = crate::leanh::lean_ctor_get(v_snd_3662_, 0);
                    crate::leanh::lean_inc(v_fst_3663_);
                    v___x_3664_ = l_Lean_NameSet_append(v_b_3659_, v_fst_3663_);
                    v___x_3665_ = 1usize;
                    v___x_3666_ = lean_usize_add(v_i_3657_, v___x_3665_);
                    v_i_3657_ = v___x_3666_;
                    v_b_3659_ = v___x_3664_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3659_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4___boxed(
    mut v_as_3668_: *mut crate::leanh::LeanObject,
    mut v_i_3669_: *mut crate::leanh::LeanObject,
    mut v_stop_3670_: *mut crate::leanh::LeanObject,
    mut v_b_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3672_: usize = 0;
    let mut v_stop_boxed_3673_: usize = 0;
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3672_ = crate::leanh::lean_unbox_usize(v_i_3669_);
    crate::leanh::lean_dec(v_i_3669_);
    v_stop_boxed_3673_ = crate::leanh::lean_unbox_usize(v_stop_3670_);
    crate::leanh::lean_dec(v_stop_3670_);
    v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v_as_3668_, v_i_boxed_3672_, v_stop_boxed_3673_, v_b_3671_);
    crate::leanh::lean_dec_ref(v_as_3668_);
    return v_res_3674_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__1;
    v___x_3679_ = l_Lean_MessageData_ofFormat(v___x_3678_);
    return v___x_3679_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680_ = crate::leanh::lean_box(1);
    v___x_3681_ = l_Lean_MessageData_ofFormat(v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8(
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v_fst_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: f64 = 0.0;
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3712_: u8 = 0;
    let mut v_isSharedCheck_3713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3682_) == 0 {
                    v___x_3684_ = l_List_reverse___redArg(v_a_3683_);
                    return v___x_3684_;
                } else {
                    v_head_3685_ = crate::leanh::lean_ctor_get(v_a_3682_, 0);
                    v_tail_3686_ = crate::leanh::lean_ctor_get(v_a_3682_, 1);
                    v_isSharedCheck_3713_ = (!crate::leanh::lean_is_exclusive(v_a_3682_)) as u8;
                    if v_isSharedCheck_3713_ == 0 {
                        v___x_3688_ = v_a_3682_;
                        v_isShared_3689_ = v_isSharedCheck_3713_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3686_);
                        crate::leanh::lean_inc(v_head_3685_);
                        crate::leanh::lean_dec(v_a_3682_);
                        v___x_3688_ = crate::leanh::lean_box(0);
                        v_isShared_3689_ = v_isSharedCheck_3713_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3690_ = crate::leanh::lean_ctor_get(v_head_3685_, 0);
                v_snd_3691_ = crate::leanh::lean_ctor_get(v_head_3685_, 1);
                v_isSharedCheck_3712_ = (!crate::leanh::lean_is_exclusive(v_head_3685_)) as u8;
                if v_isSharedCheck_3712_ == 0 {
                    v___x_3693_ = v_head_3685_;
                    v_isShared_3694_ = v_isSharedCheck_3712_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3691_);
                    crate::leanh::lean_inc(v_fst_3690_);
                    crate::leanh::lean_dec(v_head_3685_);
                    v___x_3693_ = crate::leanh::lean_box(0);
                    v_isShared_3694_ = v_isSharedCheck_3712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3695_ = l_Lean_MessageData_ofName(v_fst_3690_);
                v___x_3696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2_once), _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__2);
                if v_isShared_3694_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3693_, 7);
                    crate::leanh::lean_ctor_set(v___x_3693_, 1, v___x_3696_);
                    crate::leanh::lean_ctor_set(v___x_3693_, 0, v___x_3695_);
                    v___x_3698_ = v___x_3693_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3711_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3711_, 1, v___x_3696_);
                    v___x_3698_ = v_reuseFailAlloc_3711_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3699_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3_once), _init_l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8___closed__3);
                v___x_3700_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3700_, 0, v___x_3698_);
                crate::leanh::lean_ctor_set(v___x_3700_, 1, v___x_3699_);
                v___x_3701_ = crate::leanh::lean_unbox_float(v_snd_3691_);
                crate::leanh::lean_dec(v_snd_3691_);
                v___x_3702_ = lean_float_to_string(v___x_3701_);
                v___x_3703_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3703_, 0, v___x_3702_);
                v___x_3704_ = l_Lean_MessageData_ofFormat(v___x_3703_);
                v___x_3705_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3700_);
                crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
                v___x_3706_ = l_Lean_MessageData_paren(v___x_3705_);
                if v_isShared_3689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3688_, 1, v_a_3683_);
                    crate::leanh::lean_ctor_set(v___x_3688_, 0, v___x_3706_);
                    v___x_3708_ = v___x_3688_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_a_3683_);
                    v___x_3708_ = v_reuseFailAlloc_3710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3682_ = v_tail_3686_;
                v_a_3683_ = v___x_3708_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__2;
    v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__4;
    v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
    return v___x_3722_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__6;
    v___x_3725_ = l_Lean_stringToMessageData(v___x_3724_);
    return v___x_3725_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(
    mut v___f_3726_: *mut crate::leanh::LeanObject,
    mut v_fst_3727_: *mut crate::leanh::LeanObject,
    mut v_c_3728_: f64,
    mut v___x_3729_: *mut crate::leanh::LeanObject,
    mut v___x_3730_: *mut crate::leanh::LeanObject,
    mut v_fst_3731_: *mut crate::leanh::LeanObject,
    mut v_snd_3732_: *mut crate::leanh::LeanObject,
    mut v_fst_3733_: *mut crate::leanh::LeanObject,
    mut v_score_3734_: *mut crate::leanh::LeanObject,
    mut v___x_3735_: *mut crate::leanh::LeanObject,
    mut v_____r_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: f64 = 0.0;
    let mut v___x_3746_: f64 = 0.0;
    let mut v___x_3747_: f64 = 0.0;
    let mut v___x_3748_: f64 = 0.0;
    let mut v___x_3749_: f64 = 0.0;
    let mut v___x_3750_: f64 = 0.0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: usize = 0;
    let mut v___y_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3765_: usize = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: u8 = 0;
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3769_: usize = 0;
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: usize = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: usize = 0;
    let mut v___y_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut v___x_3780_: u8 = 0;
    let mut v___x_3781_: usize = 0;
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: usize = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3790_: usize = 0;
    let mut v___y_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: usize = 0;
    let mut v___y_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___y_3804_: u8 = 0;
    let mut v___y_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3808_: usize = 0;
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: u8 = 0;
    let mut v___y_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3815_: usize = 0;
    let mut v___x_3816_: usize = 0;
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3820_: usize = 0;
    let mut v___x_3821_: f64 = 0.0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v_options_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3831_: u8 = 0;
    let mut v_inheritedTraceOptions_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: u8 = 0;
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3837_: usize = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_a_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3888_: u8 = 0;
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3738_);
                crate::leanh::lean_inc_ref(v___y_3737_);
                v___x_3865_ = crate::leanh::lean_apply_3(
                    v___f_3726_,
                    v___y_3737_,
                    v___y_3738_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3865_) == 0 {
                    v_a_3866_ = crate::leanh::lean_ctor_get(v___x_3865_, 0);
                    crate::leanh::lean_inc(v_a_3866_);
                    crate::leanh::lean_dec_ref_known(v___x_3865_, 1);
                    v___x_3867_ = (crate::leanh::lean_unbox(v_a_3866_) as u8);
                    crate::leanh::lean_dec(v_a_3866_);
                    if v___x_3867_ == 0 {
                        v___y_3813_ = v___y_3737_;
                        v___y_3814_ = v___y_3738_;
                        state = 7;
                        continue;
                    } else {
                        v___x_3868_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__7);
                        v___x_3869_ = crate::leanh::lean_box(0);
                        v___x_3870_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__10(v___x_3869_, v_fst_3731_);
                        v___x_3871_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__11(v___x_3870_, v___x_3869_);
                        v___x_3872_ = l_Lean_MessageData_ofList(v___x_3871_);
                        v___x_3873_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3873_, 0, v___x_3868_);
                        crate::leanh::lean_ctor_set(v___x_3873_, 1, v___x_3872_);
                        v___x_3874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
                        v___x_3875_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3875_, 0, v___x_3873_);
                        crate::leanh::lean_ctor_set(v___x_3875_, 1, v___x_3874_);
                        crate::leanh::lean_inc(v___x_3735_);
                        v___x_3876_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_3735_, v___x_3875_, v___y_3737_, v___y_3738_);
                        if crate::leanh::lean_obj_tag(v___x_3876_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3876_, 1);
                            v___y_3813_ = v___y_3737_;
                            v___y_3814_ = v___y_3738_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3735_);
                            crate::leanh::lean_dec_ref(v_score_3734_);
                            crate::leanh::lean_dec(v_fst_3733_);
                            crate::leanh::lean_dec(v_snd_3732_);
                            crate::leanh::lean_dec(v_fst_3731_);
                            crate::leanh::lean_dec(v___x_3730_);
                            crate::leanh::lean_dec(v___x_3729_);
                            crate::leanh::lean_dec(v_fst_3727_);
                            v_a_3877_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
                            v_isSharedCheck_3884_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3876_)) as u8;
                            if v_isSharedCheck_3884_ == 0 {
                                v___x_3879_ = v___x_3876_;
                                v_isShared_3880_ = v_isSharedCheck_3884_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3877_);
                                crate::leanh::lean_dec(v___x_3876_);
                                v___x_3879_ = crate::leanh::lean_box(0);
                                v_isShared_3880_ = v_isSharedCheck_3884_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3735_);
                    crate::leanh::lean_dec_ref(v_score_3734_);
                    crate::leanh::lean_dec(v_fst_3733_);
                    crate::leanh::lean_dec(v_snd_3732_);
                    crate::leanh::lean_dec(v_fst_3731_);
                    crate::leanh::lean_dec(v___x_3730_);
                    crate::leanh::lean_dec(v___x_3729_);
                    crate::leanh::lean_dec(v_fst_3727_);
                    v_a_3885_ = crate::leanh::lean_ctor_get(v___x_3865_, 0);
                    v_isSharedCheck_3892_ = (!crate::leanh::lean_is_exclusive(v___x_3865_)) as u8;
                    if v_isSharedCheck_3892_ == 0 {
                        v___x_3887_ = v___x_3865_;
                        v_isShared_3888_ = v_isSharedCheck_3892_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3885_);
                        crate::leanh::lean_dec(v___x_3865_);
                        v___x_3887_ = crate::leanh::lean_box(0);
                        v_isShared_3888_ = v_isSharedCheck_3892_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3745_ = lean_float_of_nat(v___y_3743_);
                v___x_3746_ = crate::leanh::lean_unbox_float(v_fst_3727_);
                v___x_3747_ = lean_float_sub(v___x_3745_, v___x_3746_);
                v___x_3748_ = lean_float_div(v___x_3747_, v_c_3728_);
                v___x_3749_ = crate::leanh::lean_unbox_float(v_fst_3727_);
                crate::leanh::lean_dec(v_fst_3727_);
                v___x_3750_ = lean_float_add(v___x_3749_, v___x_3748_);
                v___x_3751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3751_, 0, v___y_3744_);
                crate::leanh::lean_ctor_set(v___x_3751_, 1, v___y_3742_);
                v___x_3752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3752_, 0, v___y_3741_);
                crate::leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
                v___x_3753_ = crate::leanh::lean_box_float(v___x_3750_);
                v___x_3754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3753_);
                crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3752_);
                v___x_3755_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3755_, 0, v___x_3729_);
                crate::leanh::lean_ctor_set(v___x_3755_, 1, v___x_3754_);
                v___x_3756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3755_);
                v___x_3757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3757_, 0, v___x_3756_);
                return v___x_3757_;
            }
            2 => {
                v_sz_3765_ = lean_array_size(v___y_3761_);
                v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__3(v_sz_3765_, v___y_3763_, v___y_3761_);
                v___x_3767_ = lean_nat_dec_lt(v___x_3730_, v___y_3759_);
                crate::leanh::lean_dec(v___x_3730_);
                if v___x_3767_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3762_);
                    crate::leanh::lean_dec(v___y_3759_);
                    v___y_3741_ = v___x_3766_;
                    v___y_3742_ = v___y_3764_;
                    v___y_3743_ = v___y_3760_;
                    v___y_3744_ = v_fst_3731_;
                    state = 1;
                    continue;
                } else {
                    v___x_3768_ = lean_nat_dec_le(v___y_3759_, v___y_3759_);
                    if v___x_3768_ == 0 {
                        if v___x_3767_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_3762_);
                            crate::leanh::lean_dec(v___y_3759_);
                            v___y_3741_ = v___x_3766_;
                            v___y_3742_ = v___y_3764_;
                            v___y_3743_ = v___y_3760_;
                            v___y_3744_ = v_fst_3731_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3769_ = lean_usize_of_nat(v___y_3759_);
                            crate::leanh::lean_dec(v___y_3759_);
                            v___x_3770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v___y_3762_, v___y_3763_, v___x_3769_, v_fst_3731_);
                            crate::leanh::lean_dec_ref(v___y_3762_);
                            v___y_3741_ = v___x_3766_;
                            v___y_3742_ = v___y_3764_;
                            v___y_3743_ = v___y_3760_;
                            v___y_3744_ = v___x_3770_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3771_ = lean_usize_of_nat(v___y_3759_);
                        crate::leanh::lean_dec(v___y_3759_);
                        v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__4(v___y_3762_, v___y_3763_, v___x_3771_, v_fst_3731_);
                        crate::leanh::lean_dec_ref(v___y_3762_);
                        v___y_3741_ = v___x_3766_;
                        v___y_3742_ = v___y_3764_;
                        v___y_3743_ = v___y_3760_;
                        v___y_3744_ = v___x_3772_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3778_ = lean_array_get_size(v___y_3777_);
                v___x_3779_ = lean_nat_dec_lt(v___x_3730_, v___x_3778_);
                if v___x_3779_ == 0 {
                    v___y_3759_ = v___x_3778_;
                    v___y_3760_ = v___y_3775_;
                    v___y_3761_ = v___y_3774_;
                    v___y_3762_ = v___y_3777_;
                    v___y_3763_ = v___y_3776_;
                    v___y_3764_ = v_snd_3732_;
                    state = 2;
                    continue;
                } else {
                    v___x_3780_ = lean_nat_dec_le(v___x_3778_, v___x_3778_);
                    if v___x_3780_ == 0 {
                        if v___x_3779_ == 0 {
                            v___y_3759_ = v___x_3778_;
                            v___y_3760_ = v___y_3775_;
                            v___y_3761_ = v___y_3774_;
                            v___y_3762_ = v___y_3777_;
                            v___y_3763_ = v___y_3776_;
                            v___y_3764_ = v_snd_3732_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3781_ = lean_usize_of_nat(v___x_3778_);
                            v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v___y_3777_, v___y_3776_, v___x_3781_, v_snd_3732_);
                            v___y_3759_ = v___x_3778_;
                            v___y_3760_ = v___y_3775_;
                            v___y_3761_ = v___y_3774_;
                            v___y_3762_ = v___y_3777_;
                            v___y_3763_ = v___y_3776_;
                            v___y_3764_ = v___x_3782_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_3783_ = lean_usize_of_nat(v___x_3778_);
                        v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__5(v___y_3777_, v___y_3776_, v___x_3783_, v_snd_3732_);
                        v___y_3759_ = v___x_3778_;
                        v___y_3760_ = v___y_3775_;
                        v___y_3761_ = v___y_3774_;
                        v___y_3762_ = v___y_3777_;
                        v___y_3763_ = v___y_3776_;
                        v___y_3764_ = v___x_3784_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3793_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v___y_3791_, v___y_3786_, v___y_3789_, v___y_3792_);
                crate::leanh::lean_dec(v___y_3792_);
                crate::leanh::lean_dec(v___y_3791_);
                v___y_3774_ = v___y_3788_;
                v___y_3775_ = v___y_3787_;
                v___y_3776_ = v___y_3790_;
                v___y_3777_ = v___x_3793_;
                state = 3;
                continue;
            }
            5 => {
                v___x_3802_ = lean_nat_dec_le(v___y_3801_, v___y_3795_);
                if v___x_3802_ == 0 {
                    crate::leanh::lean_dec(v___y_3795_);
                    crate::leanh::lean_inc(v___y_3801_);
                    v___y_3786_ = v___y_3796_;
                    v___y_3787_ = v___y_3798_;
                    v___y_3788_ = v___y_3797_;
                    v___y_3789_ = v___y_3801_;
                    v___y_3790_ = v___y_3800_;
                    v___y_3791_ = v___y_3799_;
                    v___y_3792_ = v___y_3801_;
                    state = 4;
                    continue;
                } else {
                    v___y_3786_ = v___y_3796_;
                    v___y_3787_ = v___y_3798_;
                    v___y_3788_ = v___y_3797_;
                    v___y_3789_ = v___y_3801_;
                    v___y_3790_ = v___y_3800_;
                    v___y_3791_ = v___y_3799_;
                    v___y_3792_ = v___y_3795_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_3809_ = crate::leanh::lean_unsigned_to_nat(1);
                if v___y_3804_ == 0 {
                    v___x_3810_ = lean_nat_sub(v___y_3807_, v___x_3809_);
                    v___x_3811_ = lean_nat_dec_le(v___x_3730_, v___x_3810_);
                    if v___x_3811_ == 0 {
                        crate::leanh::lean_inc(v___x_3810_);
                        v___y_3795_ = v___x_3810_;
                        v___y_3796_ = v___y_3805_;
                        v___y_3797_ = v___y_3806_;
                        v___y_3798_ = v___x_3809_;
                        v___y_3799_ = v___y_3807_;
                        v___y_3800_ = v___y_3808_;
                        v___y_3801_ = v___x_3810_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_3730_);
                        v___y_3795_ = v___x_3810_;
                        v___y_3796_ = v___y_3805_;
                        v___y_3797_ = v___y_3806_;
                        v___y_3798_ = v___x_3809_;
                        v___y_3799_ = v___y_3807_;
                        v___y_3800_ = v___y_3808_;
                        v___y_3801_ = v___x_3730_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3807_);
                    v___y_3774_ = v___y_3806_;
                    v___y_3775_ = v___x_3809_;
                    v___y_3776_ = v___y_3808_;
                    v___y_3777_ = v___y_3805_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v_sz_3815_ = lean_array_size(v_fst_3733_);
                v___x_3816_ = 0usize;
                crate::leanh::lean_inc(v_fst_3733_);
                crate::leanh::lean_inc(v_fst_3731_);
                v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__1(v_score_3734_, v_fst_3731_, v_sz_3815_, v___x_3816_, v_fst_3733_);
                v_bs_3818_ = lean_mk_empty_array_with_capacity(v___x_3730_);
                crate::leanh::lean_inc_ref(v_bs_3818_);
                v___x_3819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3819_, 0, v_bs_3818_);
                crate::leanh::lean_ctor_set(v___x_3819_, 1, v_bs_3818_);
                v_sz_3820_ = lean_array_size(v___x_3817_);
                v___x_3821_ = crate::leanh::lean_unbox_float(v_fst_3727_);
                v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__2(v___x_3821_, v___x_3817_, v_sz_3820_, v___x_3816_, v___x_3819_);
                crate::leanh::lean_dec_ref(v___x_3817_);
                v_fst_3823_ = crate::leanh::lean_ctor_get(v___x_3822_, 0);
                v_snd_3824_ = crate::leanh::lean_ctor_get(v___x_3822_, 1);
                v_isSharedCheck_3864_ = (!crate::leanh::lean_is_exclusive(v___x_3822_)) as u8;
                if v_isSharedCheck_3864_ == 0 {
                    v___x_3826_ = v___x_3822_;
                    v_isShared_3827_ = v_isSharedCheck_3864_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3824_);
                    crate::leanh::lean_inc(v_fst_3823_);
                    crate::leanh::lean_dec(v___x_3822_);
                    v___x_3826_ = crate::leanh::lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3864_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3828_ = lean_array_get_size(v_fst_3823_);
                v___x_3829_ = lean_nat_dec_eq(v___x_3828_, v___x_3730_);
                if v___x_3829_ == 0 {
                    crate::leanh::lean_del_object(v___x_3826_);
                    crate::leanh::lean_dec(v_fst_3733_);
                    v_options_3830_ = crate::leanh::lean_ctor_get(v___y_3813_, 2);
                    v_hasTrace_3831_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3830_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3831_ == 0 {
                        crate::leanh::lean_dec(v___x_3735_);
                        v___y_3804_ = v___x_3829_;
                        v___y_3805_ = v_fst_3823_;
                        v___y_3806_ = v_snd_3824_;
                        v___y_3807_ = v___x_3828_;
                        v___y_3808_ = v___x_3816_;
                        state = 6;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3832_ =
                            crate::leanh::lean_ctor_get(v___y_3813_, 13);
                        v___x_3833_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1;
                        crate::leanh::lean_inc(v___x_3735_);
                        v___x_3834_ = l_Lean_Name_append(v___x_3833_, v___x_3735_);
                        v___x_3835_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3832_,
                            v_options_3830_,
                            v___x_3834_,
                        );
                        crate::leanh::lean_dec(v___x_3834_);
                        if v___x_3835_ == 0 {
                            crate::leanh::lean_dec(v___x_3735_);
                            v___y_3804_ = v___x_3829_;
                            v___y_3805_ = v_fst_3823_;
                            v___y_3806_ = v_snd_3824_;
                            v___y_3807_ = v___x_3828_;
                            v___y_3808_ = v___x_3816_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__3);
                            v_sz_3837_ = lean_array_size(v_fst_3823_);
                            crate::leanh::lean_inc(v_fst_3823_);
                            v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__7(v_sz_3837_, v___x_3816_, v_fst_3823_);
                            v___x_3839_ = lean_array_to_list(v___x_3838_);
                            v___x_3840_ = crate::leanh::lean_box(0);
                            v___x_3841_ = l_List_mapTR_loop___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__8(v___x_3839_, v___x_3840_);
                            v___x_3842_ = l_Lean_MessageData_ofList(v___x_3841_);
                            v___x_3843_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3843_, 0, v___x_3836_);
                            crate::leanh::lean_ctor_set(v___x_3843_, 1, v___x_3842_);
                            v___x_3844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
                            v___x_3845_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3845_, 0, v___x_3843_);
                            crate::leanh::lean_ctor_set(v___x_3845_, 1, v___x_3844_);
                            v___x_3846_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_3735_, v___x_3845_, v___y_3813_, v___y_3814_);
                            if crate::leanh::lean_obj_tag(v___x_3846_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3846_, 1);
                                v___y_3804_ = v___x_3829_;
                                v___y_3805_ = v_fst_3823_;
                                v___y_3806_ = v_snd_3824_;
                                v___y_3807_ = v___x_3828_;
                                v___y_3808_ = v___x_3816_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_snd_3824_);
                                crate::leanh::lean_dec(v_fst_3823_);
                                crate::leanh::lean_dec(v_snd_3732_);
                                crate::leanh::lean_dec(v_fst_3731_);
                                crate::leanh::lean_dec(v___x_3730_);
                                crate::leanh::lean_dec(v___x_3729_);
                                crate::leanh::lean_dec(v_fst_3727_);
                                v_a_3847_ = crate::leanh::lean_ctor_get(v___x_3846_, 0);
                                v_isSharedCheck_3854_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3846_)) as u8;
                                if v_isSharedCheck_3854_ == 0 {
                                    v___x_3849_ = v___x_3846_;
                                    v_isShared_3850_ = v_isSharedCheck_3854_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3847_);
                                    crate::leanh::lean_dec(v___x_3846_);
                                    v___x_3849_ = crate::leanh::lean_box(0);
                                    v_isShared_3850_ = v_isSharedCheck_3854_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3824_);
                    crate::leanh::lean_dec(v_fst_3823_);
                    crate::leanh::lean_dec(v___x_3735_);
                    crate::leanh::lean_dec(v___x_3730_);
                    crate::leanh::lean_dec(v___x_3729_);
                    crate::leanh::lean_inc(v_snd_3732_);
                    v___x_3855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3855_, 0, v_snd_3732_);
                    if v_isShared_3827_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3826_, 1, v_snd_3732_);
                        crate::leanh::lean_ctor_set(v___x_3826_, 0, v_fst_3731_);
                        v___x_3857_ = v___x_3826_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_fst_3731_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_snd_3732_);
                        v___x_3857_ = v_reuseFailAlloc_3863_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3850_ == 0 {
                    v___x_3852_ = v___x_3849_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
                    v___x_3852_ = v_reuseFailAlloc_3853_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3852_;
            }
            11 => {
                v___x_3858_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3858_, 0, v_fst_3733_);
                crate::leanh::lean_ctor_set(v___x_3858_, 1, v___x_3857_);
                v___x_3859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3859_, 0, v_fst_3727_);
                crate::leanh::lean_ctor_set(v___x_3859_, 1, v___x_3858_);
                v___x_3860_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3860_, 0, v___x_3855_);
                crate::leanh::lean_ctor_set(v___x_3860_, 1, v___x_3859_);
                v___x_3861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3861_, 0, v___x_3860_);
                v___x_3862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3862_, 0, v___x_3861_);
                return v___x_3862_;
            }
            12 => {
                if v_isShared_3880_ == 0 {
                    v___x_3882_ = v___x_3879_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
                    v___x_3882_ = v_reuseFailAlloc_3883_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3882_;
            }
            14 => {
                if v_isShared_3888_ == 0 {
                    v___x_3890_ = v___x_3887_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
                    v___x_3890_ = v_reuseFailAlloc_3891_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___boxed(
    mut v___f_3893_: *mut crate::leanh::LeanObject,
    mut v_fst_3894_: *mut crate::leanh::LeanObject,
    mut v_c_3895_: *mut crate::leanh::LeanObject,
    mut v___x_3896_: *mut crate::leanh::LeanObject,
    mut v___x_3897_: *mut crate::leanh::LeanObject,
    mut v_fst_3898_: *mut crate::leanh::LeanObject,
    mut v_snd_3899_: *mut crate::leanh::LeanObject,
    mut v_fst_3900_: *mut crate::leanh::LeanObject,
    mut v_score_3901_: *mut crate::leanh::LeanObject,
    mut v___x_3902_: *mut crate::leanh::LeanObject,
    mut v_____r_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_3907_: f64 = 0.0;
    let mut v_res_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_3907_ = crate::leanh::lean_unbox_float(v_c_3895_);
    crate::leanh::lean_dec_ref(v_c_3895_);
    v_res_3908_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_3893_, v_fst_3894_, v_c_boxed_3907_, v___x_3896_, v___x_3897_, v_fst_3898_, v_snd_3899_, v_fst_3900_, v_score_3901_, v___x_3902_, v_____r_3903_, v___y_3904_, v___y_3905_);
    crate::leanh::lean_dec(v___y_3905_);
    crate::leanh::lean_dec_ref(v___y_3904_);
    return v_res_3908_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(
    mut v___x_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3914_: u8 = 0;
    v_options_3913_ = crate::leanh::lean_ctor_get(v___y_3910_, 2);
    v_hasTrace_3914_ = crate::leanh::lean_ctor_get_uint8(
        v_options_3913_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3914_ == 0 {
        let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3909_);
        v___x_3915_ = crate::leanh::lean_box((v_hasTrace_3914_) as usize);
        v___x_3916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3916_, 0, v___x_3915_);
        return v___x_3916_;
    } else {
        let mut v_inheritedTraceOptions_3917_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3920_: u8 = 0;
        let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3917_ = crate::leanh::lean_ctor_get(v___y_3910_, 13);
        v___x_3918_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__1;
        v___x_3919_ = l_Lean_Name_append(v___x_3918_, v___x_3909_);
        v___x_3920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3917_,
            v_options_3913_,
            v___x_3919_,
        );
        crate::leanh::lean_dec(v___x_3919_);
        v___x_3921_ = crate::leanh::lean_box((v___x_3920_) as usize);
        v___x_3922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3922_, 0, v___x_3921_);
        return v___x_3922_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0___boxed(
    mut v___x_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3927_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(v___x_3923_, v___y_3924_, v___y_3925_);
    crate::leanh::lean_dec(v___y_3925_);
    crate::leanh::lean_dec_ref(v___y_3924_);
    return v_res_3927_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__1;
    v___x_3932_ = l_Lean_stringToMessageData(v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(
    mut v_score_3933_: *mut crate::leanh::LeanObject,
    mut v_c_3934_: f64,
    mut v_maxSuggestions_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v_a_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_snd_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v_snd_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3970_: u8 = 0;
    let mut v_fst_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v_fst_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: f64 = 0.0;
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4018_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4022_: u8 = 0;
    let mut v_a_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4030_: u8 = 0;
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: u8 = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_unused_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v_unused_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3961_ = crate::leanh::lean_ctor_get(v_a_3936_, 1);
                v_isSharedCheck_4040_ = (!crate::leanh::lean_is_exclusive(v_a_3936_)) as u8;
                if v_isSharedCheck_4040_ == 0 {
                    v_unused_4041_ = crate::leanh::lean_ctor_get(v_a_3936_, 0);
                    crate::leanh::lean_dec(v_unused_4041_);
                    v___x_3963_ = v_a_3936_;
                    v_isShared_3964_ = v_isSharedCheck_4040_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3961_);
                    crate::leanh::lean_dec(v_a_3936_);
                    v___x_3963_ = crate::leanh::lean_box(0);
                    v_isShared_3964_ = v_isSharedCheck_4040_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3941_) == 0 {
                    v_a_3942_ = crate::leanh::lean_ctor_get(v___y_3941_, 0);
                    v_isSharedCheck_3952_ = (!crate::leanh::lean_is_exclusive(v___y_3941_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3944_ = v___y_3941_;
                        v_isShared_3945_ = v_isSharedCheck_3952_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3942_);
                        crate::leanh::lean_dec(v___y_3941_);
                        v___x_3944_ = crate::leanh::lean_box(0);
                        v_isShared_3945_ = v_isSharedCheck_3952_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_score_3933_);
                    v_a_3953_ = crate::leanh::lean_ctor_get(v___y_3941_, 0);
                    v_isSharedCheck_3960_ = (!crate::leanh::lean_is_exclusive(v___y_3941_)) as u8;
                    if v_isSharedCheck_3960_ == 0 {
                        v___x_3955_ = v___y_3941_;
                        v_isShared_3956_ = v_isSharedCheck_3960_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3953_);
                        crate::leanh::lean_dec(v___y_3941_);
                        v___x_3955_ = crate::leanh::lean_box(0);
                        v_isShared_3956_ = v_isSharedCheck_3960_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3942_) == 0 {
                    crate::leanh::lean_dec_ref(v_score_3933_);
                    v_a_3946_ = crate::leanh::lean_ctor_get(v_a_3942_, 0);
                    crate::leanh::lean_inc(v_a_3946_);
                    crate::leanh::lean_dec_ref_known(v_a_3942_, 1);
                    if v_isShared_3945_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3944_, 0, v_a_3946_);
                        v___x_3948_ = v___x_3944_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3946_);
                        v___x_3948_ = v_reuseFailAlloc_3949_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3944_);
                    v_a_3950_ = crate::leanh::lean_ctor_get(v_a_3942_, 0);
                    crate::leanh::lean_inc(v_a_3950_);
                    crate::leanh::lean_dec_ref_known(v_a_3942_, 1);
                    v_a_3936_ = v_a_3950_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3948_;
            }
            4 => {
                if v_isShared_3956_ == 0 {
                    v___x_3958_ = v___x_3955_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
                    v___x_3958_ = v_reuseFailAlloc_3959_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3958_;
            }
            6 => {
                v_snd_3965_ = crate::leanh::lean_ctor_get(v_snd_3961_, 1);
                crate::leanh::lean_inc(v_snd_3965_);
                v_snd_3966_ = crate::leanh::lean_ctor_get(v_snd_3965_, 1);
                crate::leanh::lean_inc(v_snd_3966_);
                v_fst_3967_ = crate::leanh::lean_ctor_get(v_snd_3961_, 0);
                v_isSharedCheck_4038_ = (!crate::leanh::lean_is_exclusive(v_snd_3961_)) as u8;
                if v_isSharedCheck_4038_ == 0 {
                    v_unused_4039_ = crate::leanh::lean_ctor_get(v_snd_3961_, 1);
                    crate::leanh::lean_dec(v_unused_4039_);
                    v___x_3969_ = v_snd_3961_;
                    v_isShared_3970_ = v_isSharedCheck_4038_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3967_);
                    crate::leanh::lean_dec(v_snd_3961_);
                    v___x_3969_ = crate::leanh::lean_box(0);
                    v_isShared_3970_ = v_isSharedCheck_4038_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_3971_ = crate::leanh::lean_ctor_get(v_snd_3965_, 0);
                v_isSharedCheck_4036_ = (!crate::leanh::lean_is_exclusive(v_snd_3965_)) as u8;
                if v_isSharedCheck_4036_ == 0 {
                    v_unused_4037_ = crate::leanh::lean_ctor_get(v_snd_3965_, 1);
                    crate::leanh::lean_dec(v_unused_4037_);
                    v___x_3973_ = v_snd_3965_;
                    v_isShared_3974_ = v_isSharedCheck_4036_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3971_);
                    crate::leanh::lean_dec(v_snd_3965_);
                    v___x_3973_ = crate::leanh::lean_box(0);
                    v_isShared_3974_ = v_isSharedCheck_4036_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_3975_ = crate::leanh::lean_ctor_get(v_snd_3966_, 0);
                v_snd_3976_ = crate::leanh::lean_ctor_get(v_snd_3966_, 1);
                v_isSharedCheck_4035_ = (!crate::leanh::lean_is_exclusive(v_snd_3966_)) as u8;
                if v_isSharedCheck_4035_ == 0 {
                    v___x_3978_ = v_snd_3966_;
                    v_isShared_3979_ = v_isSharedCheck_4035_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3976_);
                    crate::leanh::lean_inc(v_fst_3975_);
                    crate::leanh::lean_dec(v_snd_3966_);
                    v___x_3978_ = crate::leanh::lean_box(0);
                    v_isShared_3979_ = v_isSharedCheck_4035_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3980_ = crate::leanh::lean_box(0);
                v___x_3981_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4031_ = lean_array_get_size(v_fst_3971_);
                v___x_4032_ = lean_nat_dec_lt(v___x_3981_, v___x_4031_);
                if v___x_4032_ == 0 {
                    v___y_3983_ = v___x_4032_;
                    state = 10;
                    continue;
                } else {
                    v___x_4033_ = lean_array_get_size(v_snd_3976_);
                    v___x_4034_ = lean_nat_dec_lt(v___x_4033_, v_maxSuggestions_3935_);
                    v___y_3983_ = v___x_4034_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3983_ == 0 {
                    crate::leanh::lean_dec_ref(v_score_3933_);
                    if v_isShared_3979_ == 0 {
                        v___x_3985_ = v___x_3978_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3996_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_fst_3975_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_snd_3976_);
                        v___x_3985_ = v_reuseFailAlloc_3996_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3978_);
                    crate::leanh::lean_del_object(v___x_3973_);
                    crate::leanh::lean_del_object(v___x_3969_);
                    crate::leanh::lean_del_object(v___x_3963_);
                    v___x_3997_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn___closed__1_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_;
                    v___f_3998_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__0;
                    v___x_3999_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__0(v___x_3997_, v___y_3937_, v___y_3938_);
                    if crate::leanh::lean_obj_tag(v___x_3999_) == 0 {
                        v_a_4000_ = crate::leanh::lean_ctor_get(v___x_3999_, 0);
                        crate::leanh::lean_inc(v_a_4000_);
                        crate::leanh::lean_dec_ref_known(v___x_3999_, 1);
                        v___x_4001_ = (crate::leanh::lean_unbox(v_a_4000_) as u8);
                        crate::leanh::lean_dec(v_a_4000_);
                        if v___x_4001_ == 0 {
                            v___x_4002_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc_ref(v_score_3933_);
                            v___x_4003_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_3998_, v_fst_3967_, v_c_3934_, v___x_3980_, v___x_3981_, v_fst_3975_, v_snd_3976_, v_fst_3971_, v_score_3933_, v___x_3997_, v___x_4002_, v___y_3937_, v___y_3938_);
                            v___y_3941_ = v___x_4003_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4004_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___closed__2);
                            v___x_4005_ = crate::leanh::lean_unbox_float(v_fst_3967_);
                            v___x_4006_ = lean_float_to_string(v___x_4005_);
                            v___x_4007_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4006_);
                            v___x_4008_ = l_Lean_MessageData_ofFormat(v___x_4007_);
                            v___x_4009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4004_);
                            crate::leanh::lean_ctor_set(v___x_4009_, 1, v___x_4008_);
                            v___x_4010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1___closed__5);
                            v___x_4011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4011_, 0, v___x_4009_);
                            crate::leanh::lean_ctor_set(v___x_4011_, 1, v___x_4010_);
                            v___x_4012_ = l_Lean_addTrace___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__9(v___x_3997_, v___x_4011_, v___y_3937_, v___y_3938_);
                            if crate::leanh::lean_obj_tag(v___x_4012_) == 0 {
                                v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                                crate::leanh::lean_inc(v_a_4013_);
                                crate::leanh::lean_dec_ref_known(v___x_4012_, 1);
                                crate::leanh::lean_inc_ref(v_score_3933_);
                                v___x_4014_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___lam__1(v___f_3998_, v_fst_3967_, v_c_3934_, v___x_3980_, v___x_3981_, v_fst_3975_, v_snd_3976_, v_fst_3971_, v_score_3933_, v___x_3997_, v_a_4013_, v___y_3937_, v___y_3938_);
                                v___y_3941_ = v___x_4014_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_snd_3976_);
                                crate::leanh::lean_dec(v_fst_3975_);
                                crate::leanh::lean_dec(v_fst_3971_);
                                crate::leanh::lean_dec(v_fst_3967_);
                                crate::leanh::lean_dec_ref(v_score_3933_);
                                v_a_4015_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                                v_isSharedCheck_4022_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4012_)) as u8;
                                if v_isSharedCheck_4022_ == 0 {
                                    v___x_4017_ = v___x_4012_;
                                    v_isShared_4018_ = v_isSharedCheck_4022_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4015_);
                                    crate::leanh::lean_dec(v___x_4012_);
                                    v___x_4017_ = crate::leanh::lean_box(0);
                                    v_isShared_4018_ = v_isSharedCheck_4022_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_3976_);
                        crate::leanh::lean_dec(v_fst_3975_);
                        crate::leanh::lean_dec(v_fst_3971_);
                        crate::leanh::lean_dec(v_fst_3967_);
                        crate::leanh::lean_dec_ref(v_score_3933_);
                        v_a_4023_ = crate::leanh::lean_ctor_get(v___x_3999_, 0);
                        v_isSharedCheck_4030_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3999_)) as u8;
                        if v_isSharedCheck_4030_ == 0 {
                            v___x_4025_ = v___x_3999_;
                            v_isShared_4026_ = v_isSharedCheck_4030_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4023_);
                            crate::leanh::lean_dec(v___x_3999_);
                            v___x_4025_ = crate::leanh::lean_box(0);
                            v_isShared_4026_ = v_isSharedCheck_4030_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            11 => {
                if v_isShared_3974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3985_);
                    v___x_3987_ = v___x_3973_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3995_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_fst_3971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3995_, 1, v___x_3985_);
                    v___x_3987_ = v_reuseFailAlloc_3995_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3970_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3969_, 1, v___x_3987_);
                    v___x_3989_ = v___x_3969_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_fst_3967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3987_);
                    v___x_3989_ = v_reuseFailAlloc_3994_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3963_, 1, v___x_3989_);
                    crate::leanh::lean_ctor_set(v___x_3963_, 0, v___x_3980_);
                    v___x_3991_ = v___x_3963_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 1, v___x_3989_);
                    v___x_3991_ = v_reuseFailAlloc_3993_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3992_, 0, v___x_3991_);
                return v___x_3992_;
            }
            15 => {
                if v_isShared_4018_ == 0 {
                    v___x_4020_ = v___x_4017_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4021_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
                    v___x_4020_ = v_reuseFailAlloc_4021_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4020_;
            }
            17 => {
                if v_isShared_4026_ == 0 {
                    v___x_4028_ = v___x_4025_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4029_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
                    v___x_4028_ = v_reuseFailAlloc_4029_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg___boxed(
    mut v_score_4042_: *mut crate::leanh::LeanObject,
    mut v_c_4043_: *mut crate::leanh::LeanObject,
    mut v_maxSuggestions_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_4049_: f64 = 0.0;
    let mut v_res_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_4049_ = crate::leanh::lean_unbox_float(v_c_4043_);
    crate::leanh::lean_dec_ref(v_c_4043_);
    v_res_4050_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_4042_, v_c_boxed_4049_, v_maxSuggestions_4044_, v_a_4045_, v___y_4046_, v___y_4047_);
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    crate::leanh::lean_dec(v_maxSuggestions_4044_);
    return v_res_4050_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(
    mut v_f_4051_: *mut crate::leanh::LeanObject,
    mut v_x_4052_: *mut crate::leanh::LeanObject,
    mut v_x_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4053_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_4051_);
                    v___x_4058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4058_, 0, v_x_4052_);
                    crate::leanh::lean_ctor_set(v___x_4058_, 1, v___y_4054_);
                    v___x_4059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4058_);
                    v___x_4060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4059_);
                    return v___x_4060_;
                } else {
                    v_key_4061_ = crate::leanh::lean_ctor_get(v_x_4053_, 0);
                    crate::leanh::lean_inc(v_key_4061_);
                    v_value_4062_ = crate::leanh::lean_ctor_get(v_x_4053_, 1);
                    crate::leanh::lean_inc(v_value_4062_);
                    v_tail_4063_ = crate::leanh::lean_ctor_get(v_x_4053_, 2);
                    crate::leanh::lean_inc(v_tail_4063_);
                    crate::leanh::lean_dec_ref_known(v_x_4053_, 3);
                    crate::leanh::lean_inc_ref(v_f_4051_);
                    crate::leanh::lean_inc(v___y_4056_);
                    crate::leanh::lean_inc_ref(v___y_4055_);
                    v___x_4064_ = crate::leanh::lean_apply_6(
                        v_f_4051_,
                        v_key_4061_,
                        v_value_4062_,
                        v___y_4054_,
                        v___y_4055_,
                        v___y_4056_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4064_) == 0 {
                        v_a_4065_ = crate::leanh::lean_ctor_get(v___x_4064_, 0);
                        crate::leanh::lean_inc(v_a_4065_);
                        if crate::leanh::lean_obj_tag(v_a_4065_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_4065_, 1);
                            crate::leanh::lean_dec(v_tail_4063_);
                            crate::leanh::lean_dec_ref(v_f_4051_);
                            return v___x_4064_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4064_, 1);
                            v_a_4066_ = crate::leanh::lean_ctor_get(v_a_4065_, 0);
                            crate::leanh::lean_inc(v_a_4066_);
                            crate::leanh::lean_dec_ref_known(v_a_4065_, 1);
                            v_fst_4067_ = crate::leanh::lean_ctor_get(v_a_4066_, 0);
                            crate::leanh::lean_inc(v_fst_4067_);
                            v_snd_4068_ = crate::leanh::lean_ctor_get(v_a_4066_, 1);
                            crate::leanh::lean_inc(v_snd_4068_);
                            crate::leanh::lean_dec(v_a_4066_);
                            v_x_4052_ = v_fst_4067_;
                            v_x_4053_ = v_tail_4063_;
                            v___y_4054_ = v_snd_4068_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_4063_);
                        crate::leanh::lean_dec_ref(v_f_4051_);
                        return v___x_4064_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg___boxed(
    mut v_f_4070_: *mut crate::leanh::LeanObject,
    mut v_x_4071_: *mut crate::leanh::LeanObject,
    mut v_x_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4077_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_4070_, v_x_4071_, v_x_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
    crate::leanh::lean_dec(v___y_4075_);
    crate::leanh::lean_dec_ref(v___y_4074_);
    return v_res_4077_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg(
    mut v_f_4078_: *mut crate::leanh::LeanObject,
    mut v_as_4079_: *mut crate::leanh::LeanObject,
    mut v_i_4080_: usize,
    mut v_stop_4081_: usize,
    mut v_b_4082_: *mut crate::leanh::LeanObject,
    mut v___y_4083_: *mut crate::leanh::LeanObject,
    mut v___y_4084_: *mut crate::leanh::LeanObject,
    mut v___y_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: usize = 0;
    let mut v___x_4096_: usize = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4087_ = lean_usize_dec_eq(v_i_4080_, v_stop_4081_);
                if v___x_4087_ == 0 {
                    v___x_4088_ = lean_array_uget_borrowed(v_as_4079_, v_i_4080_);
                    v___x_4089_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_4088_);
                    crate::leanh::lean_inc_ref(v_f_4078_);
                    v___x_4090_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_4078_, v___x_4089_, v___x_4088_, v___y_4083_, v___y_4084_, v___y_4085_);
                    if crate::leanh::lean_obj_tag(v___x_4090_) == 0 {
                        v_a_4091_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
                        crate::leanh::lean_inc(v_a_4091_);
                        if crate::leanh::lean_obj_tag(v_a_4091_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_4091_, 1);
                            crate::leanh::lean_dec_ref(v_f_4078_);
                            return v___x_4090_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4090_, 1);
                            v_a_4092_ = crate::leanh::lean_ctor_get(v_a_4091_, 0);
                            crate::leanh::lean_inc(v_a_4092_);
                            crate::leanh::lean_dec_ref_known(v_a_4091_, 1);
                            v_fst_4093_ = crate::leanh::lean_ctor_get(v_a_4092_, 0);
                            crate::leanh::lean_inc(v_fst_4093_);
                            v_snd_4094_ = crate::leanh::lean_ctor_get(v_a_4092_, 1);
                            crate::leanh::lean_inc(v_snd_4094_);
                            crate::leanh::lean_dec(v_a_4092_);
                            v___x_4095_ = 1usize;
                            v___x_4096_ = lean_usize_add(v_i_4080_, v___x_4095_);
                            v_i_4080_ = v___x_4096_;
                            v_b_4082_ = v_fst_4093_;
                            v___y_4083_ = v_snd_4094_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_f_4078_);
                        return v___x_4090_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4078_);
                    v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4098_, 0, v_b_4082_);
                    crate::leanh::lean_ctor_set(v___x_4098_, 1, v___y_4083_);
                    v___x_4099_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
                    v___x_4100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4099_);
                    return v___x_4100_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg___boxed(
    mut v_f_4101_: *mut crate::leanh::LeanObject,
    mut v_as_4102_: *mut crate::leanh::LeanObject,
    mut v_i_4103_: *mut crate::leanh::LeanObject,
    mut v_stop_4104_: *mut crate::leanh::LeanObject,
    mut v_b_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4110_: usize = 0;
    let mut v_stop_boxed_4111_: usize = 0;
    let mut v_res_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4110_ = crate::leanh::lean_unbox_usize(v_i_4103_);
    crate::leanh::lean_dec(v_i_4103_);
    v_stop_boxed_4111_ = crate::leanh::lean_unbox_usize(v_stop_4104_);
    crate::leanh::lean_dec(v_stop_4104_);
    v_res_4112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg(v_f_4101_, v_as_4102_, v_i_boxed_4110_, v_stop_boxed_4111_, v_b_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
    crate::leanh::lean_dec(v___y_4108_);
    crate::leanh::lean_dec_ref(v___y_4107_);
    crate::leanh::lean_dec_ref(v_as_4102_);
    return v_res_4112_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0(
    mut v_f_4113_: *mut crate::leanh::LeanObject,
    mut v_x_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4119_);
    crate::leanh::lean_inc_ref(v___y_4118_);
    v___x_4121_ = crate::leanh::lean_apply_6(
        v_f_4113_,
        v___y_4115_,
        v___y_4116_,
        v___y_4117_,
        v___y_4118_,
        v___y_4119_,
        crate::leanh::lean_box(0),
    );
    return v___x_4121_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0___boxed(
    mut v_f_4122_: *mut crate::leanh::LeanObject,
    mut v_x_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0(v_f_4122_, v_x_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    return v_res_4130_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___redArg(
    mut v_f_4131_: *mut crate::leanh::LeanObject,
    mut v_keys_4132_: *mut crate::leanh::LeanObject,
    mut v_vals_4133_: *mut crate::leanh::LeanObject,
    mut v_i_4134_: *mut crate::leanh::LeanObject,
    mut v_acc_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4140_ = lean_array_get_size(v_keys_4132_);
                v___x_4141_ = lean_nat_dec_lt(v_i_4134_, v___x_4140_);
                if v___x_4141_ == 0 {
                    crate::leanh::lean_dec(v_i_4134_);
                    crate::leanh::lean_dec_ref(v_f_4131_);
                    v___x_4142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4142_, 0, v_acc_4135_);
                    crate::leanh::lean_ctor_set(v___x_4142_, 1, v___y_4136_);
                    v___x_4143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4143_, 0, v___x_4142_);
                    v___x_4144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4144_, 0, v___x_4143_);
                    return v___x_4144_;
                } else {
                    v_k_4145_ = lean_array_fget_borrowed(v_keys_4132_, v_i_4134_);
                    v_v_4146_ = lean_array_fget_borrowed(v_vals_4133_, v_i_4134_);
                    crate::leanh::lean_inc_ref(v_f_4131_);
                    crate::leanh::lean_inc(v___y_4138_);
                    crate::leanh::lean_inc_ref(v___y_4137_);
                    crate::leanh::lean_inc(v_v_4146_);
                    crate::leanh::lean_inc(v_k_4145_);
                    v___x_4147_ = crate::leanh::lean_apply_7(
                        v_f_4131_,
                        v_acc_4135_,
                        v_k_4145_,
                        v_v_4146_,
                        v___y_4136_,
                        v___y_4137_,
                        v___y_4138_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4147_) == 0 {
                        v_a_4148_ = crate::leanh::lean_ctor_get(v___x_4147_, 0);
                        crate::leanh::lean_inc(v_a_4148_);
                        if crate::leanh::lean_obj_tag(v_a_4148_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_4148_, 1);
                            crate::leanh::lean_dec(v_i_4134_);
                            crate::leanh::lean_dec_ref(v_f_4131_);
                            return v___x_4147_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4147_, 1);
                            v_a_4149_ = crate::leanh::lean_ctor_get(v_a_4148_, 0);
                            crate::leanh::lean_inc(v_a_4149_);
                            crate::leanh::lean_dec_ref_known(v_a_4148_, 1);
                            v_fst_4150_ = crate::leanh::lean_ctor_get(v_a_4149_, 0);
                            crate::leanh::lean_inc(v_fst_4150_);
                            v_snd_4151_ = crate::leanh::lean_ctor_get(v_a_4149_, 1);
                            crate::leanh::lean_inc(v_snd_4151_);
                            crate::leanh::lean_dec(v_a_4149_);
                            v___x_4152_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4153_ = lean_nat_add(v_i_4134_, v___x_4152_);
                            crate::leanh::lean_dec(v_i_4134_);
                            v_i_4134_ = v___x_4153_;
                            v_acc_4135_ = v_fst_4150_;
                            v___y_4136_ = v_snd_4151_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_4134_);
                        crate::leanh::lean_dec_ref(v_f_4131_);
                        return v___x_4147_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___redArg___boxed(
    mut v_f_4155_: *mut crate::leanh::LeanObject,
    mut v_keys_4156_: *mut crate::leanh::LeanObject,
    mut v_vals_4157_: *mut crate::leanh::LeanObject,
    mut v_i_4158_: *mut crate::leanh::LeanObject,
    mut v_acc_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___redArg(v_f_4155_, v_keys_4156_, v_vals_4157_, v_i_4158_, v_acc_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
    crate::leanh::lean_dec(v___y_4162_);
    crate::leanh::lean_dec_ref(v___y_4161_);
    crate::leanh::lean_dec_ref(v_vals_4157_);
    crate::leanh::lean_dec_ref(v_keys_4156_);
    return v_res_4164_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(
    mut v_f_4165_: *mut crate::leanh::LeanObject,
    mut v_x_4166_: *mut crate::leanh::LeanObject,
    mut v_x_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: usize = 0;
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: usize = 0;
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v_ks_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4166_) == 0 {
                    v_es_4172_ = crate::leanh::lean_ctor_get(v_x_4166_, 0);
                    v_isSharedCheck_4196_ = (!crate::leanh::lean_is_exclusive(v_x_4166_)) as u8;
                    if v_isSharedCheck_4196_ == 0 {
                        v___x_4174_ = v_x_4166_;
                        v_isShared_4175_ = v_isSharedCheck_4196_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_4172_);
                        crate::leanh::lean_dec(v_x_4166_);
                        v___x_4174_ = crate::leanh::lean_box(0);
                        v_isShared_4175_ = v_isSharedCheck_4196_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_4197_ = crate::leanh::lean_ctor_get(v_x_4166_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4197_);
                    v_vs_4198_ = crate::leanh::lean_ctor_get(v_x_4166_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4198_);
                    crate::leanh::lean_dec_ref_known(v_x_4166_, 2);
                    v___x_4199_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4200_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___redArg(v_f_4165_, v_ks_4197_, v_vs_4198_, v___x_4199_, v_x_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                    crate::leanh::lean_dec_ref(v_vs_4198_);
                    crate::leanh::lean_dec_ref(v_ks_4197_);
                    return v___x_4200_;
                }
            }
            1 => {
                v___x_4176_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4177_ = lean_array_get_size(v_es_4172_);
                v___x_4178_ = lean_nat_dec_lt(v___x_4176_, v___x_4177_);
                if v___x_4178_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_4172_);
                    crate::leanh::lean_dec_ref(v_f_4165_);
                    v___x_4179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4179_, 0, v_x_4167_);
                    crate::leanh::lean_ctor_set(v___x_4179_, 1, v___y_4168_);
                    if v_isShared_4175_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4174_, 1);
                        crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4179_);
                        v___x_4181_ = v___x_4174_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4179_);
                        v___x_4181_ = v_reuseFailAlloc_4183_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4184_ = lean_nat_dec_le(v___x_4177_, v___x_4177_);
                    if v___x_4184_ == 0 {
                        if v___x_4178_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_4172_);
                            crate::leanh::lean_dec_ref(v_f_4165_);
                            v___x_4185_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4185_, 0, v_x_4167_);
                            crate::leanh::lean_ctor_set(v___x_4185_, 1, v___y_4168_);
                            if v_isShared_4175_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4174_, 1);
                                crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4185_);
                                v___x_4187_ = v___x_4174_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4189_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v___x_4185_);
                                v___x_4187_ = v_reuseFailAlloc_4189_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4174_);
                            v___x_4190_ = 0usize;
                            v___x_4191_ = lean_usize_of_nat(v___x_4177_);
                            v___x_4192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg(v_f_4165_, v_es_4172_, v___x_4190_, v___x_4191_, v_x_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                            crate::leanh::lean_dec_ref(v_es_4172_);
                            return v___x_4192_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4174_);
                        v___x_4193_ = 0usize;
                        v___x_4194_ = lean_usize_of_nat(v___x_4177_);
                        v___x_4195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg(v_f_4165_, v_es_4172_, v___x_4193_, v___x_4194_, v_x_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
                        crate::leanh::lean_dec_ref(v_es_4172_);
                        return v___x_4195_;
                    }
                }
            }
            2 => {
                v___x_4182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4181_);
                return v___x_4182_;
            }
            3 => {
                v___x_4188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4188_, 0, v___x_4187_);
                return v___x_4188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg(
    mut v_f_4201_: *mut crate::leanh::LeanObject,
    mut v_as_4202_: *mut crate::leanh::LeanObject,
    mut v_i_4203_: usize,
    mut v_stop_4204_: usize,
    mut v_b_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: usize = 0;
    let mut v___x_4214_: usize = 0;
    let mut v___y_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4222_ = lean_usize_dec_eq(v_i_4203_, v_stop_4204_);
                if v___x_4222_ == 0 {
                    v___x_4223_ = lean_array_uget_borrowed(v_as_4202_, v_i_4203_);
                    match crate::leanh::lean_obj_tag(v___x_4223_) {
                        0 => {
                            v_key_4224_ = crate::leanh::lean_ctor_get(v___x_4223_, 0);
                            v_val_4225_ = crate::leanh::lean_ctor_get(v___x_4223_, 1);
                            crate::leanh::lean_inc_ref(v_f_4201_);
                            crate::leanh::lean_inc(v___y_4208_);
                            crate::leanh::lean_inc_ref(v___y_4207_);
                            crate::leanh::lean_inc(v_val_4225_);
                            crate::leanh::lean_inc(v_key_4224_);
                            v___x_4226_ = crate::leanh::lean_apply_7(
                                v_f_4201_,
                                v_b_4205_,
                                v_key_4224_,
                                v_val_4225_,
                                v___y_4206_,
                                v___y_4207_,
                                v___y_4208_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_4217_ = v___x_4226_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_4227_ = crate::leanh::lean_ctor_get(v___x_4223_, 0);
                            crate::leanh::lean_inc(v_node_4227_);
                            crate::leanh::lean_inc_ref(v_f_4201_);
                            v___x_4228_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v_f_4201_, v_node_4227_, v_b_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
                            v___y_4217_ = v___x_4228_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_fst_4211_ = v_b_4205_;
                            v_snd_4212_ = v___y_4206_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4201_);
                    v___x_4229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4229_, 0, v_b_4205_);
                    crate::leanh::lean_ctor_set(v___x_4229_, 1, v___y_4206_);
                    v___x_4230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4230_, 0, v___x_4229_);
                    v___x_4231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4231_, 0, v___x_4230_);
                    return v___x_4231_;
                }
            }
            1 => {
                v___x_4213_ = 1usize;
                v___x_4214_ = lean_usize_add(v_i_4203_, v___x_4213_);
                v_i_4203_ = v___x_4214_;
                v_b_4205_ = v_fst_4211_;
                v___y_4206_ = v_snd_4212_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4217_) == 0 {
                    v_a_4218_ = crate::leanh::lean_ctor_get(v___y_4217_, 0);
                    if crate::leanh::lean_obj_tag(v_a_4218_) == 0 {
                        crate::leanh::lean_dec_ref(v_f_4201_);
                        return v___y_4217_;
                    } else {
                        crate::leanh::lean_inc_ref(v_a_4218_);
                        crate::leanh::lean_dec_ref_known(v___y_4217_, 1);
                        v_a_4219_ = crate::leanh::lean_ctor_get(v_a_4218_, 0);
                        crate::leanh::lean_inc(v_a_4219_);
                        crate::leanh::lean_dec_ref_known(v_a_4218_, 1);
                        v_fst_4220_ = crate::leanh::lean_ctor_get(v_a_4219_, 0);
                        crate::leanh::lean_inc(v_fst_4220_);
                        v_snd_4221_ = crate::leanh::lean_ctor_get(v_a_4219_, 1);
                        crate::leanh::lean_inc(v_snd_4221_);
                        crate::leanh::lean_dec(v_a_4219_);
                        v_fst_4211_ = v_fst_4220_;
                        v_snd_4212_ = v_snd_4221_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4201_);
                    return v___y_4217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg___boxed(
    mut v_f_4232_: *mut crate::leanh::LeanObject,
    mut v_as_4233_: *mut crate::leanh::LeanObject,
    mut v_i_4234_: *mut crate::leanh::LeanObject,
    mut v_stop_4235_: *mut crate::leanh::LeanObject,
    mut v_b_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4241_: usize = 0;
    let mut v_stop_boxed_4242_: usize = 0;
    let mut v_res_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4241_ = crate::leanh::lean_unbox_usize(v_i_4234_);
    crate::leanh::lean_dec(v_i_4234_);
    v_stop_boxed_4242_ = crate::leanh::lean_unbox_usize(v_stop_4235_);
    crate::leanh::lean_dec(v_stop_4235_);
    v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg(v_f_4232_, v_as_4233_, v_i_boxed_4241_, v_stop_boxed_4242_, v_b_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
    crate::leanh::lean_dec(v___y_4239_);
    crate::leanh::lean_dec_ref(v___y_4238_);
    crate::leanh::lean_dec_ref(v_as_4233_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg___boxed(
    mut v_f_4244_: *mut crate::leanh::LeanObject,
    mut v_x_4245_: *mut crate::leanh::LeanObject,
    mut v_x_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
    mut v___y_4249_: *mut crate::leanh::LeanObject,
    mut v___y_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4251_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v_f_4244_, v_x_4245_, v_x_4246_, v___y_4247_, v___y_4248_, v___y_4249_);
    crate::leanh::lean_dec(v___y_4249_);
    crate::leanh::lean_dec_ref(v___y_4248_);
    return v_res_4251_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(
    mut v_map_4252_: *mut crate::leanh::LeanObject,
    mut v_f_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4258_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
    crate::leanh::lean_closure_set(v___f_4258_, 0, v_f_4253_);
    v___x_4259_ = crate::leanh::lean_box(0);
    v___x_4260_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v___f_4258_, v_map_4252_, v___x_4259_, v___y_4254_, v___y_4255_, v___y_4256_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg___boxed(
    mut v_map_4261_: *mut crate::leanh::LeanObject,
    mut v_f_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4267_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_4261_, v_f_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
    crate::leanh::lean_dec(v___y_4265_);
    crate::leanh::lean_dec_ref(v___y_4264_);
    return v_res_4267_;
}
pub unsafe fn l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(
    mut v_s_4268_: *mut crate::leanh::LeanObject,
    mut v_f_4269_: *mut crate::leanh::LeanObject,
    mut v___y_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: u8 = 0;
    v_map_u2081_4274_ = crate::leanh::lean_ctor_get(v_s_4268_, 0);
    crate::leanh::lean_inc_ref(v_map_u2081_4274_);
    v_map_u2082_4275_ = crate::leanh::lean_ctor_get(v_s_4268_, 1);
    crate::leanh::lean_inc_ref(v_map_u2082_4275_);
    crate::leanh::lean_dec_ref(v_s_4268_);
    v_buckets_4276_ = crate::leanh::lean_ctor_get(v_map_u2081_4274_, 1);
    crate::leanh::lean_inc_ref(v_buckets_4276_);
    crate::leanh::lean_dec_ref(v_map_u2081_4274_);
    v___x_4277_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4278_ = lean_array_get_size(v_buckets_4276_);
    v___x_4279_ = lean_nat_dec_lt(v___x_4277_, v___x_4278_);
    if v___x_4279_ == 0 {
        let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_buckets_4276_);
        v___x_4280_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_u2082_4275_, v_f_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
        return v___x_4280_;
    } else {
        let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4282_: u8 = 0;
        v___x_4281_ = crate::leanh::lean_box(0);
        v___x_4282_ = lean_nat_dec_le(v___x_4278_, v___x_4278_);
        if v___x_4282_ == 0 {
            if v___x_4279_ == 0 {
                let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_buckets_4276_);
                v___x_4283_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_u2082_4275_, v_f_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
                return v___x_4283_;
            } else {
                let mut v___x_4284_: usize = 0;
                let mut v___x_4285_: usize = 0;
                let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4284_ = 0usize;
                v___x_4285_ = lean_usize_of_nat(v___x_4278_);
                crate::leanh::lean_inc_ref(v_f_4269_);
                v___x_4286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg(v_f_4269_, v_buckets_4276_, v___x_4284_, v___x_4285_, v___x_4281_, v___y_4270_, v___y_4271_, v___y_4272_);
                crate::leanh::lean_dec_ref(v_buckets_4276_);
                if crate::leanh::lean_obj_tag(v___x_4286_) == 0 {
                    let mut v_a_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_4287_ = crate::leanh::lean_ctor_get(v___x_4286_, 0);
                    crate::leanh::lean_inc(v_a_4287_);
                    if crate::leanh::lean_obj_tag(v_a_4287_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_4287_, 1);
                        crate::leanh::lean_dec_ref(v_map_u2082_4275_);
                        crate::leanh::lean_dec_ref(v_f_4269_);
                        return v___x_4286_;
                    } else {
                        let mut v_a_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref_known(v___x_4286_, 1);
                        v_a_4288_ = crate::leanh::lean_ctor_get(v_a_4287_, 0);
                        crate::leanh::lean_inc(v_a_4288_);
                        crate::leanh::lean_dec_ref_known(v_a_4287_, 1);
                        v_snd_4289_ = crate::leanh::lean_ctor_get(v_a_4288_, 1);
                        crate::leanh::lean_inc(v_snd_4289_);
                        crate::leanh::lean_dec(v_a_4288_);
                        v___x_4290_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_u2082_4275_, v_f_4269_, v_snd_4289_, v___y_4271_, v___y_4272_);
                        return v___x_4290_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_map_u2082_4275_);
                    crate::leanh::lean_dec_ref(v_f_4269_);
                    return v___x_4286_;
                }
            }
        } else {
            let mut v___x_4291_: usize = 0;
            let mut v___x_4292_: usize = 0;
            let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4291_ = 0usize;
            v___x_4292_ = lean_usize_of_nat(v___x_4278_);
            crate::leanh::lean_inc_ref(v_f_4269_);
            v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg(v_f_4269_, v_buckets_4276_, v___x_4291_, v___x_4292_, v___x_4281_, v___y_4270_, v___y_4271_, v___y_4272_);
            crate::leanh::lean_dec_ref(v_buckets_4276_);
            if crate::leanh::lean_obj_tag(v___x_4293_) == 0 {
                let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4293_, 0);
                crate::leanh::lean_inc(v_a_4294_);
                if crate::leanh::lean_obj_tag(v_a_4294_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_4294_, 1);
                    crate::leanh::lean_dec_ref(v_map_u2082_4275_);
                    crate::leanh::lean_dec_ref(v_f_4269_);
                    return v___x_4293_;
                } else {
                    let mut v_a_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_4293_, 1);
                    v_a_4295_ = crate::leanh::lean_ctor_get(v_a_4294_, 0);
                    crate::leanh::lean_inc(v_a_4295_);
                    crate::leanh::lean_dec_ref_known(v_a_4294_, 1);
                    v_snd_4296_ = crate::leanh::lean_ctor_get(v_a_4295_, 1);
                    crate::leanh::lean_inc(v_snd_4296_);
                    crate::leanh::lean_dec(v_a_4295_);
                    v___x_4297_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_u2082_4275_, v_f_4269_, v_snd_4296_, v___y_4271_, v___y_4272_);
                    return v___x_4297_;
                }
            } else {
                crate::leanh::lean_dec_ref(v_map_u2082_4275_);
                crate::leanh::lean_dec_ref(v_f_4269_);
                return v___x_4293_;
            }
        }
    }
}
pub unsafe fn l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg___boxed(
    mut v_s_4298_: *mut crate::leanh::LeanObject,
    mut v_f_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v_s_4298_, v_f_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
    crate::leanh::lean_dec(v___y_4302_);
    crate::leanh::lean_dec_ref(v___y_4301_);
    return v_res_4304_;
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(
    mut v_initialRelevant_4309_: *mut crate::leanh::LeanObject,
    mut v_score_4310_: *mut crate::leanh::LeanObject,
    mut v_accept_4311_: *mut crate::leanh::LeanObject,
    mut v_maxSuggestions_4312_: *mut crate::leanh::LeanObject,
    mut v_p_4313_: f64,
    mut v_c_4314_: f64,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v_fst_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut v_a_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut v_a_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4318_ = lean_st_ref_get(v_a_4316_);
                v_env_4319_ = crate::leanh::lean_ctor_get(v___x_4318_, 0);
                crate::leanh::lean_inc_ref(v_env_4319_);
                crate::leanh::lean_dec(v___x_4318_);
                v___f_4320_ = crate::leanh::lean_alloc_closure(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_4320_, 0, v_accept_4311_);
                v___x_4321_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__0;
                v___x_4322_ = l_Lean_Environment_constants(v_env_4319_);
                v___x_4323_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v___x_4322_, v___f_4320_, v___x_4321_, v_a_4315_, v_a_4316_);
                if crate::leanh::lean_obj_tag(v___x_4323_) == 0 {
                    v_a_4324_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                    crate::leanh::lean_inc(v_a_4324_);
                    crate::leanh::lean_dec_ref_known(v___x_4323_, 1);
                    v___x_4325_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___closed__1;
                    if crate::leanh::lean_obj_tag(v_a_4324_) == 0 {
                        v_a_4360_ = crate::leanh::lean_ctor_get(v_a_4324_, 0);
                        crate::leanh::lean_inc(v_a_4360_);
                        crate::leanh::lean_dec_ref_known(v_a_4324_, 1);
                        v_a_4327_ = v_a_4360_;
                        state = 1;
                        continue;
                    } else {
                        v_a_4361_ = crate::leanh::lean_ctor_get(v_a_4324_, 0);
                        crate::leanh::lean_inc(v_a_4361_);
                        crate::leanh::lean_dec_ref_known(v_a_4324_, 1);
                        v_snd_4362_ = crate::leanh::lean_ctor_get(v_a_4361_, 1);
                        crate::leanh::lean_inc(v_snd_4362_);
                        crate::leanh::lean_dec(v_a_4361_);
                        v_a_4327_ = v_snd_4362_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_score_4310_);
                    crate::leanh::lean_dec(v_initialRelevant_4309_);
                    v_a_4363_ = crate::leanh::lean_ctor_get(v___x_4323_, 0);
                    v_isSharedCheck_4370_ = (!crate::leanh::lean_is_exclusive(v___x_4323_)) as u8;
                    if v_isSharedCheck_4370_ == 0 {
                        v___x_4365_ = v___x_4323_;
                        v_isShared_4366_ = v_isSharedCheck_4370_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4363_);
                        crate::leanh::lean_dec(v___x_4323_);
                        v___x_4365_ = crate::leanh::lean_box(0);
                        v_isShared_4366_ = v_isSharedCheck_4370_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4328_ = crate::leanh::lean_box(0);
                v___x_4329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4329_, 0, v_initialRelevant_4309_);
                crate::leanh::lean_ctor_set(v___x_4329_, 1, v___x_4325_);
                v___x_4330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4330_, 0, v_a_4327_);
                crate::leanh::lean_ctor_set(v___x_4330_, 1, v___x_4329_);
                v___x_4331_ = crate::leanh::lean_box_float(v_p_4313_);
                v___x_4332_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4332_, 0, v___x_4331_);
                crate::leanh::lean_ctor_set(v___x_4332_, 1, v___x_4330_);
                v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4333_, 0, v___x_4328_);
                crate::leanh::lean_ctor_set(v___x_4333_, 1, v___x_4332_);
                v___x_4334_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_4310_, v_c_4314_, v_maxSuggestions_4312_, v___x_4333_, v_a_4315_, v_a_4316_);
                if crate::leanh::lean_obj_tag(v___x_4334_) == 0 {
                    v_a_4335_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4351_ = (!crate::leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4351_ == 0 {
                        v___x_4337_ = v___x_4334_;
                        v_isShared_4338_ = v_isSharedCheck_4351_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4335_);
                        crate::leanh::lean_dec(v___x_4334_);
                        v___x_4337_ = crate::leanh::lean_box(0);
                        v_isShared_4338_ = v_isSharedCheck_4351_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4352_ = crate::leanh::lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4359_ = (!crate::leanh::lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4359_ == 0 {
                        v___x_4354_ = v___x_4334_;
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4352_);
                        crate::leanh::lean_dec(v___x_4334_);
                        v___x_4354_ = crate::leanh::lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4339_ = crate::leanh::lean_ctor_get(v_a_4335_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4339_) == 0 {
                    v_snd_4340_ = crate::leanh::lean_ctor_get(v_a_4335_, 1);
                    crate::leanh::lean_inc(v_snd_4340_);
                    crate::leanh::lean_dec(v_a_4335_);
                    v_snd_4341_ = crate::leanh::lean_ctor_get(v_snd_4340_, 1);
                    crate::leanh::lean_inc(v_snd_4341_);
                    crate::leanh::lean_dec(v_snd_4340_);
                    v_snd_4342_ = crate::leanh::lean_ctor_get(v_snd_4341_, 1);
                    crate::leanh::lean_inc(v_snd_4342_);
                    crate::leanh::lean_dec(v_snd_4341_);
                    v_snd_4343_ = crate::leanh::lean_ctor_get(v_snd_4342_, 1);
                    crate::leanh::lean_inc(v_snd_4343_);
                    crate::leanh::lean_dec(v_snd_4342_);
                    if v_isShared_4338_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4337_, 0, v_snd_4343_);
                        v___x_4345_ = v___x_4337_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_snd_4343_);
                        v___x_4345_ = v_reuseFailAlloc_4346_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4339_);
                    crate::leanh::lean_dec(v_a_4335_);
                    v_val_4347_ = crate::leanh::lean_ctor_get(v_fst_4339_, 0);
                    crate::leanh::lean_inc(v_val_4347_);
                    crate::leanh::lean_dec_ref_known(v_fst_4339_, 1);
                    if v_isShared_4338_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4337_, 0, v_val_4347_);
                        v___x_4349_ = v___x_4337_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_val_4347_);
                        v___x_4349_ = v_reuseFailAlloc_4350_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4345_;
            }
            4 => {
                return v___x_4349_;
            }
            5 => {
                if v_isShared_4355_ == 0 {
                    v___x_4357_ = v___x_4354_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
                    v___x_4357_ = v_reuseFailAlloc_4358_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4357_;
            }
            7 => {
                if v_isShared_4366_ == 0 {
                    v___x_4368_ = v___x_4365_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
                    v___x_4368_ = v_reuseFailAlloc_4369_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo___boxed(
    mut v_initialRelevant_4371_: *mut crate::leanh::LeanObject,
    mut v_score_4372_: *mut crate::leanh::LeanObject,
    mut v_accept_4373_: *mut crate::leanh::LeanObject,
    mut v_maxSuggestions_4374_: *mut crate::leanh::LeanObject,
    mut v_p_4375_: *mut crate::leanh::LeanObject,
    mut v_c_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_boxed_4380_: f64 = 0.0;
    let mut v_c_boxed_4381_: f64 = 0.0;
    let mut v_res_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_boxed_4380_ = crate::leanh::lean_unbox_float(v_p_4375_);
    crate::leanh::lean_dec_ref(v_p_4375_);
    v_c_boxed_4381_ = crate::leanh::lean_unbox_float(v_c_4376_);
    crate::leanh::lean_dec_ref(v_c_4376_);
    v_res_4382_ = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(
        v_initialRelevant_4371_,
        v_score_4372_,
        v_accept_4373_,
        v_maxSuggestions_4374_,
        v_p_boxed_4380_,
        v_c_boxed_4381_,
        v_a_4377_,
        v_a_4378_,
    );
    crate::leanh::lean_dec(v_a_4378_);
    crate::leanh::lean_dec_ref(v_a_4377_);
    crate::leanh::lean_dec(v_maxSuggestions_4374_);
    return v_res_4382_;
}
pub unsafe fn l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0(
    mut v_00_u03b2_4383_: *mut crate::leanh::LeanObject,
    mut v_s_4384_: *mut crate::leanh::LeanObject,
    mut v_f_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___redArg(v_s_4384_, v_f_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    return v___x_4390_;
}
pub unsafe fn l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0___boxed(
    mut v_00_u03b2_4391_: *mut crate::leanh::LeanObject,
    mut v_s_4392_: *mut crate::leanh::LeanObject,
    mut v_f_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0(v_00_u03b2_4391_, v_s_4392_, v_f_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
    crate::leanh::lean_dec(v___y_4396_);
    crate::leanh::lean_dec_ref(v___y_4395_);
    return v_res_4398_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6(
    mut v_n_4399_: *mut crate::leanh::LeanObject,
    mut v_as_4400_: *mut crate::leanh::LeanObject,
    mut v_lo_4401_: *mut crate::leanh::LeanObject,
    mut v_hi_4402_: *mut crate::leanh::LeanObject,
    mut v_w_4403_: *mut crate::leanh::LeanObject,
    mut v_hlo_4404_: *mut crate::leanh::LeanObject,
    mut v_hhi_4405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___redArg(v_n_4399_, v_as_4400_, v_lo_4401_, v_hi_4402_);
    return v___x_4406_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6___boxed(
    mut v_n_4407_: *mut crate::leanh::LeanObject,
    mut v_as_4408_: *mut crate::leanh::LeanObject,
    mut v_lo_4409_: *mut crate::leanh::LeanObject,
    mut v_hi_4410_: *mut crate::leanh::LeanObject,
    mut v_w_4411_: *mut crate::leanh::LeanObject,
    mut v_hlo_4412_: *mut crate::leanh::LeanObject,
    mut v_hhi_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6(v_n_4407_, v_as_4408_, v_lo_4409_, v_hi_4410_, v_w_4411_, v_hlo_4412_, v_hhi_4413_);
    crate::leanh::lean_dec(v_hi_4410_);
    crate::leanh::lean_dec(v_n_4407_);
    return v_res_4414_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12(
    mut v_score_4415_: *mut crate::leanh::LeanObject,
    mut v_c_4416_: f64,
    mut v_maxSuggestions_4417_: *mut crate::leanh::LeanObject,
    mut v_inst_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
    mut v___y_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___redArg(v_score_4415_, v_c_4416_, v_maxSuggestions_4417_, v_a_4419_, v___y_4420_, v___y_4421_);
    return v___x_4423_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12___boxed(
    mut v_score_4424_: *mut crate::leanh::LeanObject,
    mut v_c_4425_: *mut crate::leanh::LeanObject,
    mut v_maxSuggestions_4426_: *mut crate::leanh::LeanObject,
    mut v_inst_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_4432_: f64 = 0.0;
    let mut v_res_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_4432_ = crate::leanh::lean_unbox_float(v_c_4425_);
    crate::leanh::lean_dec_ref(v_c_4425_);
    v_res_4433_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__12(v_score_4424_, v_c_boxed_4432_, v_maxSuggestions_4426_, v_inst_4427_, v_a_4428_, v___y_4429_, v___y_4430_);
    crate::leanh::lean_dec(v___y_4430_);
    crate::leanh::lean_dec_ref(v___y_4429_);
    crate::leanh::lean_dec(v_maxSuggestions_4426_);
    return v_res_4433_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0(
    mut v_00_u03b2_4434_: *mut crate::leanh::LeanObject,
    mut v_f_4435_: *mut crate::leanh::LeanObject,
    mut v_x_4436_: *mut crate::leanh::LeanObject,
    mut v_x_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___redArg(v_f_4435_, v_x_4436_, v_x_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
    return v___x_4442_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0___boxed(
    mut v_00_u03b2_4443_: *mut crate::leanh::LeanObject,
    mut v_f_4444_: *mut crate::leanh::LeanObject,
    mut v_x_4445_: *mut crate::leanh::LeanObject,
    mut v_x_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4451_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__0(v_00_u03b2_4443_, v_f_4444_, v_x_4445_, v_x_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
    crate::leanh::lean_dec(v___y_4449_);
    crate::leanh::lean_dec_ref(v___y_4448_);
    return v_res_4451_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1(
    mut v_00_u03b2_4452_: *mut crate::leanh::LeanObject,
    mut v_map_4453_: *mut crate::leanh::LeanObject,
    mut v_f_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___redArg(v_map_4453_, v_f_4454_, v___y_4455_, v___y_4456_, v___y_4457_);
    return v___x_4459_;
}
pub unsafe fn l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1___boxed(
    mut v_00_u03b2_4460_: *mut crate::leanh::LeanObject,
    mut v_map_4461_: *mut crate::leanh::LeanObject,
    mut v_f_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4467_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1(v_00_u03b2_4460_, v_map_4461_, v_f_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
    crate::leanh::lean_dec(v___y_4465_);
    crate::leanh::lean_dec_ref(v___y_4464_);
    return v_res_4467_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2(
    mut v_00_u03b2_4468_: *mut crate::leanh::LeanObject,
    mut v_f_4469_: *mut crate::leanh::LeanObject,
    mut v_as_4470_: *mut crate::leanh::LeanObject,
    mut v_i_4471_: usize,
    mut v_stop_4472_: usize,
    mut v_b_4473_: *mut crate::leanh::LeanObject,
    mut v___y_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___redArg(v_f_4469_, v_as_4470_, v_i_4471_, v_stop_4472_, v_b_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
    return v___x_4478_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2___boxed(
    mut v_00_u03b2_4479_: *mut crate::leanh::LeanObject,
    mut v_f_4480_: *mut crate::leanh::LeanObject,
    mut v_as_4481_: *mut crate::leanh::LeanObject,
    mut v_i_4482_: *mut crate::leanh::LeanObject,
    mut v_stop_4483_: *mut crate::leanh::LeanObject,
    mut v_b_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4489_: usize = 0;
    let mut v_stop_boxed_4490_: usize = 0;
    let mut v_res_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4489_ = crate::leanh::lean_unbox_usize(v_i_4482_);
    crate::leanh::lean_dec(v_i_4482_);
    v_stop_boxed_4490_ = crate::leanh::lean_unbox_usize(v_stop_4483_);
    crate::leanh::lean_dec(v_stop_4483_);
    v_res_4491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__2(v_00_u03b2_4479_, v_f_4480_, v_as_4481_, v_i_boxed_4489_, v_stop_boxed_4490_, v_b_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
    crate::leanh::lean_dec(v___y_4487_);
    crate::leanh::lean_dec_ref(v___y_4486_);
    crate::leanh::lean_dec_ref(v_as_4481_);
    return v_res_4491_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9(
    mut v_n_4492_: *mut crate::leanh::LeanObject,
    mut v_lo_4493_: *mut crate::leanh::LeanObject,
    mut v_hi_4494_: *mut crate::leanh::LeanObject,
    mut v_hhi_4495_: *mut crate::leanh::LeanObject,
    mut v_pivot_4496_: *mut crate::leanh::LeanObject,
    mut v_as_4497_: *mut crate::leanh::LeanObject,
    mut v_i_4498_: *mut crate::leanh::LeanObject,
    mut v_k_4499_: *mut crate::leanh::LeanObject,
    mut v_ilo_4500_: *mut crate::leanh::LeanObject,
    mut v_ik_4501_: *mut crate::leanh::LeanObject,
    mut v_w_4502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4503_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___redArg(v_hi_4494_, v_pivot_4496_, v_as_4497_, v_i_4498_, v_k_4499_);
    return v___x_4503_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9___boxed(
    mut v_n_4504_: *mut crate::leanh::LeanObject,
    mut v_lo_4505_: *mut crate::leanh::LeanObject,
    mut v_hi_4506_: *mut crate::leanh::LeanObject,
    mut v_hhi_4507_: *mut crate::leanh::LeanObject,
    mut v_pivot_4508_: *mut crate::leanh::LeanObject,
    mut v_as_4509_: *mut crate::leanh::LeanObject,
    mut v_i_4510_: *mut crate::leanh::LeanObject,
    mut v_k_4511_: *mut crate::leanh::LeanObject,
    mut v_ilo_4512_: *mut crate::leanh::LeanObject,
    mut v_ik_4513_: *mut crate::leanh::LeanObject,
    mut v_w_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__6_spec__9(v_n_4504_, v_lo_4505_, v_hi_4506_, v_hhi_4507_, v_pivot_4508_, v_as_4509_, v_i_4510_, v_k_4511_, v_ilo_4512_, v_ik_4513_, v_w_4514_);
    crate::leanh::lean_dec_ref(v_pivot_4508_);
    crate::leanh::lean_dec(v_hi_4506_);
    crate::leanh::lean_dec(v_lo_4505_);
    crate::leanh::lean_dec(v_n_4504_);
    return v_res_4515_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2___redArg(
    mut v_map_4516_: *mut crate::leanh::LeanObject,
    mut v_f_4517_: *mut crate::leanh::LeanObject,
    mut v_init_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4523_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v_f_4517_, v_map_4516_, v_init_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
    return v___x_4523_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_map_4524_: *mut crate::leanh::LeanObject,
    mut v_f_4525_: *mut crate::leanh::LeanObject,
    mut v_init_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2___redArg(v_map_4524_, v_f_4525_, v_init_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
    crate::leanh::lean_dec(v___y_4529_);
    crate::leanh::lean_dec_ref(v___y_4528_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2(
    mut v_00_u03c3_4532_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4533_: *mut crate::leanh::LeanObject,
    mut v_map_4534_: *mut crate::leanh::LeanObject,
    mut v_f_4535_: *mut crate::leanh::LeanObject,
    mut v_init_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4541_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v_f_4535_, v_map_4534_, v_init_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03c3_4542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4543_: *mut crate::leanh::LeanObject,
    mut v_map_4544_: *mut crate::leanh::LeanObject,
    mut v_f_4545_: *mut crate::leanh::LeanObject,
    mut v_init_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4551_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2(v_00_u03c3_4542_, v_00_u03b2_4543_, v_map_4544_, v_f_4545_, v_init_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
    crate::leanh::lean_dec(v___y_4549_);
    crate::leanh::lean_dec_ref(v___y_4548_);
    return v_res_4551_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16(
    mut v_00_u03c3_4552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4553_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4554_: *mut crate::leanh::LeanObject,
    mut v_f_4555_: *mut crate::leanh::LeanObject,
    mut v_x_4556_: *mut crate::leanh::LeanObject,
    mut v_x_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4562_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___redArg(v_f_4555_, v_x_4556_, v_x_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
    return v___x_4562_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16___boxed(
    mut v_00_u03c3_4563_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4564_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4565_: *mut crate::leanh::LeanObject,
    mut v_f_4566_: *mut crate::leanh::LeanObject,
    mut v_x_4567_: *mut crate::leanh::LeanObject,
    mut v_x_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16(v_00_u03c3_4563_, v_00_u03b1_4564_, v_00_u03b2_4565_, v_f_4566_, v_x_4567_, v_x_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
    crate::leanh::lean_dec(v___y_4571_);
    crate::leanh::lean_dec_ref(v___y_4570_);
    return v_res_4573_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19(
    mut v_00_u03b1_4574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4575_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4576_: *mut crate::leanh::LeanObject,
    mut v_f_4577_: *mut crate::leanh::LeanObject,
    mut v_as_4578_: *mut crate::leanh::LeanObject,
    mut v_i_4579_: usize,
    mut v_stop_4580_: usize,
    mut v_b_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___redArg(v_f_4577_, v_as_4578_, v_i_4579_, v_stop_4580_, v_b_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
    return v___x_4586_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19___boxed(
    mut v_00_u03b1_4587_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4588_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4589_: *mut crate::leanh::LeanObject,
    mut v_f_4590_: *mut crate::leanh::LeanObject,
    mut v_as_4591_: *mut crate::leanh::LeanObject,
    mut v_i_4592_: *mut crate::leanh::LeanObject,
    mut v_stop_4593_: *mut crate::leanh::LeanObject,
    mut v_b_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4599_: usize = 0;
    let mut v_stop_boxed_4600_: usize = 0;
    let mut v_res_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4599_ = crate::leanh::lean_unbox_usize(v_i_4592_);
    crate::leanh::lean_dec(v_i_4592_);
    v_stop_boxed_4600_ = crate::leanh::lean_unbox_usize(v_stop_4593_);
    crate::leanh::lean_dec(v_stop_4593_);
    v_res_4601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__19(v_00_u03b1_4587_, v_00_u03b2_4588_, v_00_u03c3_4589_, v_f_4590_, v_as_4591_, v_i_boxed_4599_, v_stop_boxed_4600_, v_b_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
    crate::leanh::lean_dec(v___y_4597_);
    crate::leanh::lean_dec_ref(v___y_4596_);
    crate::leanh::lean_dec_ref(v_as_4591_);
    return v_res_4601_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20(
    mut v_00_u03c3_4602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4604_: *mut crate::leanh::LeanObject,
    mut v_f_4605_: *mut crate::leanh::LeanObject,
    mut v_keys_4606_: *mut crate::leanh::LeanObject,
    mut v_vals_4607_: *mut crate::leanh::LeanObject,
    mut v_heq_4608_: *mut crate::leanh::LeanObject,
    mut v_i_4609_: *mut crate::leanh::LeanObject,
    mut v_acc_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___redArg(v_f_4605_, v_keys_4606_, v_vals_4607_, v_i_4609_, v_acc_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
    return v___x_4615_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20___boxed(
    mut v_00_u03c3_4616_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4617_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4618_: *mut crate::leanh::LeanObject,
    mut v_f_4619_: *mut crate::leanh::LeanObject,
    mut v_keys_4620_: *mut crate::leanh::LeanObject,
    mut v_vals_4621_: *mut crate::leanh::LeanObject,
    mut v_heq_4622_: *mut crate::leanh::LeanObject,
    mut v_i_4623_: *mut crate::leanh::LeanObject,
    mut v_acc_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4629_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00__private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo_spec__0_spec__1_spec__2_spec__16_spec__20(v_00_u03c3_4616_, v_00_u03b1_4617_, v_00_u03b2_4618_, v_f_4619_, v_keys_4620_, v_vals_4621_, v_heq_4622_, v_i_4623_, v_acc_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
    crate::leanh::lean_dec(v___y_4627_);
    crate::leanh::lean_dec_ref(v___y_4626_);
    crate::leanh::lean_dec_ref(v_vals_4621_);
    crate::leanh::lean_dec_ref(v_keys_4620_);
    return v_res_4629_;
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector___lam__0(
    mut v_env_4630_: *mut crate::leanh::LeanObject,
    mut v_ci_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: u8 = 0;
    v___x_4635_ = l_Lean_ConstantInfo_name(v_ci_4631_);
    v___x_4636_ = 0;
    crate::leanh::lean_inc(v___x_4635_);
    crate::leanh::lean_inc_ref(v_env_4630_);
    v___x_4637_ = l_Lean_LibrarySuggestions_isDeniedPremise(v_env_4630_, v___x_4635_, v___x_4636_);
    if v___x_4637_ == 0 {
        let mut v___x_4638_: u8 = 0;
        let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4638_ = l_Lean_wasOriginallyTheorem(v_env_4630_, v___x_4635_);
        v___x_4639_ = crate::leanh::lean_box((v___x_4638_) as usize);
        v___x_4640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4640_, 0, v___x_4639_);
        return v___x_4640_;
    } else {
        let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4635_);
        crate::leanh::lean_dec_ref(v_env_4630_);
        v___x_4641_ = crate::leanh::lean_box((v___x_4636_) as usize);
        v___x_4642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4642_, 0, v___x_4641_);
        return v___x_4642_;
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector___lam__0___boxed(
    mut v_env_4643_: *mut crate::leanh::LeanObject,
    mut v_ci_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4648_ = l_Lean_LibrarySuggestions_mepoSelector___lam__0(
        v_env_4643_,
        v_ci_4644_,
        v___y_4645_,
        v___y_4646_,
    );
    crate::leanh::lean_dec(v___y_4646_);
    crate::leanh::lean_dec_ref(v___y_4645_);
    crate::leanh::lean_dec_ref(v_ci_4644_);
    return v_res_4648_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(
    mut v_t_4649_: *mut crate::leanh::LeanObject,
    mut v_k_4650_: *mut crate::leanh::LeanObject,
    mut v_fallback_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4649_) == 0 {
                    v_k_4652_ = crate::leanh::lean_ctor_get(v_t_4649_, 1);
                    v_v_4653_ = crate::leanh::lean_ctor_get(v_t_4649_, 2);
                    v_l_4654_ = crate::leanh::lean_ctor_get(v_t_4649_, 3);
                    v_r_4655_ = crate::leanh::lean_ctor_get(v_t_4649_, 4);
                    v___x_4656_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4650_, v_k_4652_);
                    match v___x_4656_ {
                        0 => {
                            v_t_4649_ = v_l_4654_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_4653_);
                            return v_v_4653_;
                        }
                        _ => {
                            v_t_4649_ = v_r_4655_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_4651_);
                    return v_fallback_4651_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg___boxed(
    mut v_t_4659_: *mut crate::leanh::LeanObject,
    mut v_k_4660_: *mut crate::leanh::LeanObject,
    mut v_fallback_4661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_t_4659_, v_k_4660_, v_fallback_4661_);
    crate::leanh::lean_dec(v_fallback_4661_);
    crate::leanh::lean_dec(v_k_4660_);
    crate::leanh::lean_dec(v_t_4659_);
    return v_res_4662_;
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector___lam__1(
    mut v_a_4663_: *mut crate::leanh::LeanObject,
    mut v_n_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4666_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_a_4663_, v_n_4664_, v___x_4665_);
    return v___x_4666_;
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector___lam__1___boxed(
    mut v_a_4667_: *mut crate::leanh::LeanObject,
    mut v_n_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4669_ = l_Lean_LibrarySuggestions_mepoSelector___lam__1(v_a_4667_, v_n_4668_);
    crate::leanh::lean_dec(v_n_4668_);
    crate::leanh::lean_dec(v_a_4667_);
    return v_res_4669_;
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector(
    mut v_useRarity_4671_: u8,
    mut v_p_4672_: f64,
    mut v_c_4673_: f64,
    mut v_g_4674_: *mut crate::leanh::LeanObject,
    mut v_config_4675_: *mut crate::leanh::LeanObject,
    mut v_a_4676_: *mut crate::leanh::LeanObject,
    mut v_a_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
    mut v_a_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_score_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSuggestions_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v_a_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4718_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4681_ = l_Lean_MVarId_getRelevantConstants(
                    v_g_4674_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_,
                );
                if crate::leanh::lean_obj_tag(v___x_4681_) == 0 {
                    v_a_4682_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                    crate::leanh::lean_inc(v_a_4682_);
                    crate::leanh::lean_dec_ref_known(v___x_4681_, 1);
                    v___x_4683_ = lean_st_ref_get(v_a_4679_);
                    v_env_4684_ = crate::leanh::lean_ctor_get(v___x_4683_, 0);
                    crate::leanh::lean_inc_ref(v_env_4684_);
                    crate::leanh::lean_dec(v___x_4683_);
                    v___f_4685_ = crate::leanh::lean_alloc_closure(
                        l_Lean_LibrarySuggestions_mepoSelector___lam__0___boxed
                            as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4685_, 0, v_env_4684_);
                    if v_useRarity_4671_ == 0 {
                        v___x_4702_ = l_Lean_LibrarySuggestions_mepoSelector___closed__0;
                        v_score_4687_ = v___x_4702_;
                        v___y_4688_ = v_a_4678_;
                        v___y_4689_ = v_a_4679_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4703_ =
                            l_Lean_LibrarySuggestions_symbolFrequencyMap___redArg(v_a_4679_);
                        if crate::leanh::lean_obj_tag(v___x_4703_) == 0 {
                            v_a_4704_ = crate::leanh::lean_ctor_get(v___x_4703_, 0);
                            crate::leanh::lean_inc(v_a_4704_);
                            crate::leanh::lean_dec_ref_known(v___x_4703_, 1);
                            v___f_4705_ = crate::leanh::lean_alloc_closure(
                                l_Lean_LibrarySuggestions_mepoSelector___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_4705_, 0, v_a_4704_);
                            v___x_4706_ = crate::leanh::lean_alloc_closure(l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_frequencyScore___boxed as *mut core::ffi::c_void, 3, 1);
                            crate::leanh::lean_closure_set(v___x_4706_, 0, v___f_4705_);
                            v_score_4687_ = v___x_4706_;
                            v___y_4688_ = v_a_4678_;
                            v___y_4689_ = v_a_4679_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_4685_);
                            crate::leanh::lean_dec(v_a_4682_);
                            crate::leanh::lean_dec_ref(v_config_4675_);
                            v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4703_, 0);
                            v_isSharedCheck_4714_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4703_)) as u8;
                            if v_isSharedCheck_4714_ == 0 {
                                v___x_4709_ = v___x_4703_;
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4707_);
                                crate::leanh::lean_dec(v___x_4703_);
                                v___x_4709_ = crate::leanh::lean_box(0);
                                v_isShared_4710_ = v_isSharedCheck_4714_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_4675_);
                    v_a_4715_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                    v_isSharedCheck_4722_ = (!crate::leanh::lean_is_exclusive(v___x_4681_)) as u8;
                    if v_isSharedCheck_4722_ == 0 {
                        v___x_4717_ = v___x_4681_;
                        v_isShared_4718_ = v_isSharedCheck_4722_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4715_);
                        crate::leanh::lean_dec(v___x_4681_);
                        v___x_4717_ = crate::leanh::lean_box(0);
                        v_isShared_4718_ = v_isSharedCheck_4722_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_maxSuggestions_4690_ = crate::leanh::lean_ctor_get(v_config_4675_, 0);
                crate::leanh::lean_inc(v_maxSuggestions_4690_);
                crate::leanh::lean_dec_ref(v_config_4675_);
                v___x_4691_ =
                    l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_mepo(
                        v_a_4682_,
                        v_score_4687_,
                        v___f_4685_,
                        v_maxSuggestions_4690_,
                        v_p_4672_,
                        v_c_4673_,
                        v___y_4688_,
                        v___y_4689_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4691_) == 0 {
                    v_a_4692_ = crate::leanh::lean_ctor_get(v___x_4691_, 0);
                    v_isSharedCheck_4701_ = (!crate::leanh::lean_is_exclusive(v___x_4691_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v___x_4694_ = v___x_4691_;
                        v_isShared_4695_ = v_isSharedCheck_4701_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4692_);
                        crate::leanh::lean_dec(v___x_4691_);
                        v___x_4694_ = crate::leanh::lean_box(0);
                        v_isShared_4695_ = v_isSharedCheck_4701_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_maxSuggestions_4690_);
                    return v___x_4691_;
                }
            }
            2 => {
                v___x_4696_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4697_ =
                    l_Array_extract___redArg(v_a_4692_, v___x_4696_, v_maxSuggestions_4690_);
                crate::leanh::lean_dec(v_a_4692_);
                if v_isShared_4695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4694_, 0, v___x_4697_);
                    v___x_4699_ = v___x_4694_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4699_;
            }
            4 => {
                if v_isShared_4710_ == 0 {
                    v___x_4712_ = v___x_4709_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4712_;
            }
            6 => {
                if v_isShared_4718_ == 0 {
                    v___x_4720_ = v___x_4717_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
                    v___x_4720_ = v_reuseFailAlloc_4721_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LibrarySuggestions_mepoSelector___boxed(
    mut v_useRarity_4723_: *mut crate::leanh::LeanObject,
    mut v_p_4724_: *mut crate::leanh::LeanObject,
    mut v_c_4725_: *mut crate::leanh::LeanObject,
    mut v_g_4726_: *mut crate::leanh::LeanObject,
    mut v_config_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
    mut v_a_4729_: *mut crate::leanh::LeanObject,
    mut v_a_4730_: *mut crate::leanh::LeanObject,
    mut v_a_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useRarity_boxed_4733_: u8 = 0;
    let mut v_p_boxed_4734_: f64 = 0.0;
    let mut v_c_boxed_4735_: f64 = 0.0;
    let mut v_res_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useRarity_boxed_4733_ = (crate::leanh::lean_unbox(v_useRarity_4723_) as u8);
    v_p_boxed_4734_ = crate::leanh::lean_unbox_float(v_p_4724_);
    crate::leanh::lean_dec_ref(v_p_4724_);
    v_c_boxed_4735_ = crate::leanh::lean_unbox_float(v_c_4725_);
    crate::leanh::lean_dec_ref(v_c_4725_);
    v_res_4736_ = l_Lean_LibrarySuggestions_mepoSelector(
        v_useRarity_boxed_4733_,
        v_p_boxed_4734_,
        v_c_boxed_4735_,
        v_g_4726_,
        v_config_4727_,
        v_a_4728_,
        v_a_4729_,
        v_a_4730_,
        v_a_4731_,
    );
    crate::leanh::lean_dec(v_a_4731_);
    crate::leanh::lean_dec_ref(v_a_4730_);
    crate::leanh::lean_dec(v_a_4729_);
    crate::leanh::lean_dec_ref(v_a_4728_);
    return v_res_4736_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0(
    mut v_00_u03b4_4737_: *mut crate::leanh::LeanObject,
    mut v_t_4738_: *mut crate::leanh::LeanObject,
    mut v_k_4739_: *mut crate::leanh::LeanObject,
    mut v_fallback_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4741_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___redArg(v_t_4738_, v_k_4739_, v_fallback_4740_);
    return v___x_4741_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0___boxed(
    mut v_00_u03b4_4742_: *mut crate::leanh::LeanObject,
    mut v_t_4743_: *mut crate::leanh::LeanObject,
    mut v_k_4744_: *mut crate::leanh::LeanObject,
    mut v_fallback_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_LibrarySuggestions_mepoSelector_spec__0(v_00_u03b4_4742_, v_t_4743_, v_k_4744_, v_fallback_4745_);
    crate::leanh::lean_dec(v_fallback_4745_);
    crate::leanh::lean_dec(v_k_4744_);
    crate::leanh::lean_dec(v_t_4743_);
    return v_res_4746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LibrarySuggestions_MePo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_LibrarySuggestions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_LibrarySuggestions_MePo_0__Lean_LibrarySuggestions_MePo_initFn_00___x40_Lean_LibrarySuggestions_MePo_1610293474____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LibrarySuggestions_MePo(
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
pub unsafe fn initialize_Lean_LibrarySuggestions_MePo(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_LibrarySuggestions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_LibrarySuggestions_SymbolFrequency(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LibrarySuggestions_MePo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LibrarySuggestions_MePo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_LibrarySuggestions_MePo(builtin);
}
