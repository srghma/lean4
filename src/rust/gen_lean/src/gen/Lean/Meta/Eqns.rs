// Lean compiler output
// Module: Lean.Meta.Eqns
// Imports: Lean.Meta.Match.MatcherInfo Lean.DefEqAttrib Lean.Meta.RecExt Lean.Meta.LetToHave Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_isNat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::l_Lean_diagnostics;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_hasValue;
use crate::r#gen::Lean::DefEqAttrib::{
    initialize_Lean_DefEqAttrib, l_Lean_backward_defeqAttrib_useBackward, l_Lean_inferDefEqAttr,
    runtime_initialize_Lean_DefEqAttrib,
};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_contains,
    l_Lean_Environment_containsOnBranch, l_Lean_Environment_find_x3f,
    l_Lean_Environment_findAsync_x3f, l_Lean_Environment_hasUnsafe, l_Lean_Environment_header,
    l_Lean_Environment_isSafeDefinition, l_Lean_Environment_setExporting, l_Lean_Kernel_enableDiag,
    l_Lean_Kernel_isDiagnosticsEnabled, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_realizeConst,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::LetToHave::{
    initialize_Lean_Meta_LetToHave, l_Lean_Meta_letToHave, runtime_initialize_Lean_Meta_LetToHave,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, lean_is_matcher,
    runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::r#gen::Lean::Meta::RecExt::{
    initialize_Lean_Meta_RecExt, l_Lean_Meta_isRecursiveDefinition___redArg,
    runtime_initialize_Lean_Meta_RecExt,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_registerReservedNameAction;
use crate::r#gen::Lean::ResolveName::l_Lean_registerReservedNamePredicate;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_registerTraceClass, l_Lean_trace_profiler, l_Lean_trace_profiler_threshold,
    l_Lean_trace_profiler_useHeartbeats,
};
use crate::ffi::lean_task_get_own;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{lean_float_decLt, lean_float_div, lean_float_sub};
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_memcmp;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq,
    lean_string_utf8_byte_size, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 99, 107, 119, 97, 114, 100, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 113, 110, 115, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 110, 114, 101, 99, 117, 114, 115, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15861075605163525197 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7256640417235802091 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6370265134141675265 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [67, 114, 101, 97, 116, 101, 32, 102, 105, 110, 101, 45, 103, 114, 97, 105, 110, 101, 100, 32, 101, 113, 117, 97, 116, 105, 111, 110, 97, 108, 32, 108, 101, 109, 109, 97, 115, 32, 101, 118, 101, 110, 32, 102, 111, 114, 32, 110, 111, 110, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 46, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [50, 48, 50, 54, 45, 48, 51, 45, 51, 48, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10487771536523666976 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1838387699193403770 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13771802952800077724 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_backward_eqns_nonrecursive: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [100, 101, 101, 112, 82, 101, 99, 117, 114, 115, 105, 118, 101, 83, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15861075605163525197 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7256640417235802091 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15764657683406078887 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<339> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 339, m_capacity: 339, m_length: 338, m_data: [67, 114, 101, 97, 116, 101, 32, 101, 113, 117, 97, 116, 105, 111, 110, 97, 108, 32, 108, 101, 109, 109, 97, 115, 32, 102, 111, 114, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 108, 105, 107, 101, 32, 102, 111, 114, 32, 110, 111, 110, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 46, 32, 73, 102, 32, 100, 105, 115, 97, 98, 108, 101, 100, 44, 32, 109, 97, 116, 99, 104, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 115, 32, 105, 110, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 100, 111, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 99, 97, 108, 108, 115, 32, 100, 111, 32, 110, 111, 116, 32, 99, 97, 117, 115, 101, 32, 102, 117, 114, 116, 104, 101, 114, 32, 115, 112, 108, 105, 116, 115, 32, 105, 110, 32, 116, 104, 101, 32, 101, 113, 117, 97, 116, 105, 111, 110, 97, 108, 32, 108, 101, 109, 109, 97, 115, 46, 32, 84, 104, 105, 115, 32, 119, 97, 115, 32, 116, 104, 101, 32, 98, 101, 104, 97, 118, 105, 111, 114, 32, 98, 101, 102, 111, 114, 101, 32, 76, 101, 97, 110, 32, 52, 46, 49, 50, 44, 32, 97, 110, 100, 32, 116, 104, 101, 32, 112, 117, 114, 112, 111, 115, 101, 32, 111, 102, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 116, 111, 32, 104, 101, 108, 112, 32, 109, 105, 103, 114, 97, 116, 105, 110, 103, 32, 111, 108, 100, 32, 99, 111, 100, 101, 46, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10487771536523666976 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1838387699193403770 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4922256243950822370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_backward_eqns_deepRecursiveSplit: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_eqnAffectingOptions___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_eqnAffectingOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_eqnAffectingOptions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 113, 110, 79, 112, 116, 105, 111, 110, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11769309856439225366 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_eqnOptionsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_eqnThmSuffixBase___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [101, 113, 0],
    };
static mut l_Lean_Meta_eqnThmSuffixBase___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqnThmSuffixBase___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_eqnThmSuffixBase: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqnThmSuffixBase___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [101, 113, 95, 0],
    };
static mut l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_eqnThmSuffixBasePrefix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_eqn1ThmSuffix___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [101, 113, 95, 49, 0],
    };
static mut l_Lean_Meta_eqn1ThmSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqn1ThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_eqn1ThmSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqn1ThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_isEqnReservedNameSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_unfoldThmSuffix___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [101, 113, 95, 100, 101, 102, 0],
    };
static mut l_Lean_Meta_unfoldThmSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_unfoldThmSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_unfoldThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [101, 113, 95, 117, 110, 102, 111, 108, 100, 0],
    };
static mut l_Lean_Meta_eqUnfoldThmSuffix___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_eqUnfoldThmSuffix: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_eqUnfoldThmSuffix___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 101, 32, 96, 0]};
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 96, 0]};
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 100, 101, 99, 108, 97, 114, 101, 100, 0]};
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_registerGetEqnsFn___closed__0_value: crate::leanh::LeanStringObject<104> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 104,
        m_capacity: 104,
        m_length: 103,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114,
            32, 101, 113, 117, 97, 116, 105, 111, 110, 32, 103, 101, 116, 116, 101, 114, 44, 32,
            116, 104, 105, 115, 32, 107, 105, 110, 100, 32, 111, 102, 32, 101, 120, 116, 101, 110,
            115, 105, 111, 110, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 114, 101,
            103, 105, 115, 116, 101, 114, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110,
            105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Meta_registerGetEqnsFn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_registerGetEqnsFn___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_registerGetEqnsFn___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerGetEqnsFn___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedEqnsExtState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instInhabitedEqnsExtState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_eqnsExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_withEqnOptions___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_withEqnOptions___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_withEqnOptions___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_withEqnOptions___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_withEqnOptions___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_withEqnOptions___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__5: u8 = 0;
static mut l_Lean_Meta_withEqnOptions___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__6: u8 = 0;
static mut l_Lean_Meta_withEqnOptions___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_withEqnOptions___redArg___closed__7: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3_value:
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
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_saveEqnAffectingOptions___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__1: usize = 0;
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_saveEqnAffectingOptions___closed__3_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_saveEqnAffectingOptions___closed__4_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12843180897352504333 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__4_value)
            as *mut crate::leanh::LeanObject,
        6897119537390546559 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_saveEqnAffectingOptions___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6596765879240574673 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_saveEqnAffectingOptions___closed__7_value: crate::leanh::LeanStringObject<
    39,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        115, 97, 118, 105, 110, 103, 32, 101, 113, 117, 97, 116, 105, 111, 110, 45, 97, 102, 102,
        101, 99, 116, 105, 110, 103, 32, 111, 112, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32,
        0,
    ],
};
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_saveEqnAffectingOptions___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_saveEqnAffectingOptions___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0_value:
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
        105, 110, 118, 97, 108, 105, 100, 32, 117, 110, 102, 111, 108, 100, 32, 116, 104, 101, 111,
        114, 101, 109, 32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 103, 101, 110, 101, 114, 97, 116, 101,
        100, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 69, 113, 110, 115, 32, 114, 101, 115, 101, 114, 118, 101, 100, 32, 110, 97, 109, 101, 32, 97, 99, 116, 105, 111, 110, 32, 102, 111, 114, 32, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4: f64 = 0.0;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [82, 101, 115, 101, 114, 118, 101, 100, 78, 97, 109, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16524425170056508783 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: f64 = 0.0;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 113, 110, 115, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,749968656889403770 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,15657483603095650843 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11701753646630989862 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,725182179805757538 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8389707101049462615 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12404887456956650258 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11294966075339928083 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17995539394482798491 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3434129440836432099 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(
    mut v_name_3587_: *mut crate::leanh::LeanObject,
    mut v_decl_3588_: *mut crate::leanh::LeanObject,
    mut v_ref_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut v_unused_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3591_ = crate::leanh::lean_ctor_get(v_decl_3588_, 0);
                v_descr_3592_ = crate::leanh::lean_ctor_get(v_decl_3588_, 1);
                v_deprecation_x3f_3593_ = crate::leanh::lean_ctor_get(v_decl_3588_, 2);
                v___x_3594_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3595_ = (crate::leanh::lean_unbox(v_defValue_3591_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3594_, 0 as u32, v___x_3595_);
                crate::leanh::lean_inc(v_deprecation_x3f_3593_);
                crate::leanh::lean_inc_ref(v_descr_3592_);
                crate::leanh::lean_inc_n(v_name_3587_, 2);
                v___x_3596_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3596_, 0, v_name_3587_);
                crate::leanh::lean_ctor_set(v___x_3596_, 1, v_ref_3589_);
                crate::leanh::lean_ctor_set(v___x_3596_, 2, v___x_3594_);
                crate::leanh::lean_ctor_set(v___x_3596_, 3, v_descr_3592_);
                crate::leanh::lean_ctor_set(v___x_3596_, 4, v_deprecation_x3f_3593_);
                v___x_3597_ = lean_register_option(v_name_3587_, v___x_3596_);
                if crate::leanh::lean_obj_tag(v___x_3597_) == 0 {
                    v_isSharedCheck_3605_ = (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                    if v_isSharedCheck_3605_ == 0 {
                        v_unused_3606_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                        crate::leanh::lean_dec(v_unused_3606_);
                        v___x_3599_ = v___x_3597_;
                        v_isShared_3600_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3597_);
                        v___x_3599_ = crate::leanh::lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3605_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3587_);
                    v_a_3607_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                    v_isSharedCheck_3614_ = (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                    if v_isSharedCheck_3614_ == 0 {
                        v___x_3609_ = v___x_3597_;
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3607_);
                        crate::leanh::lean_dec(v___x_3597_);
                        v___x_3609_ = crate::leanh::lean_box(0);
                        v_isShared_3610_ = v_isSharedCheck_3614_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3591_);
                v___x_3601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3601_, 0, v_name_3587_);
                crate::leanh::lean_ctor_set(v___x_3601_, 1, v_defValue_3591_);
                if v_isShared_3600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3599_, 0, v___x_3601_);
                    v___x_3603_ = v___x_3599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3603_;
            }
            3 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3615_: *mut crate::leanh::LeanObject,
    mut v_decl_3616_: *mut crate::leanh::LeanObject,
    mut v_ref_3617_: *mut crate::leanh::LeanObject,
    mut v_a_3618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v_name_3615_, v_decl_3616_, v_ref_3617_);
    crate::leanh::lean_dec_ref(v_decl_3616_);
    return v_res_3619_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_;
    v___x_3649_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_;
    v___x_3650_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_;
    v___x_3651_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_3648_, v___x_3649_, v___x_3650_);
    return v___x_3651_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4____boxed(
    mut v_a_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3653_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
    return v_res_3653_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_;
    v___x_3673_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_;
    v___x_3674_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_;
    v___x_3675_ = l_Lean_Option_register___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4__spec__0(v___x_3672_, v___x_3673_, v___x_3674_);
    return v___x_3675_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4____boxed(
    mut v_a_3676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3677_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
    return v_res_3677_;
}
pub unsafe fn _init_l_Lean_Meta_eqnAffectingOptions___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3678_ = l_Lean_backward_defeqAttrib_useBackward;
    v___x_3679_ = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
    v___x_3680_ = l_Lean_Meta_backward_eqns_nonrecursive;
    v___x_3681_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_3682_ = lean_mk_empty_array_with_capacity(v___x_3681_);
    v___x_3683_ = lean_array_push(v___x_3682_, v___x_3680_);
    v___x_3684_ = lean_array_push(v___x_3683_, v___x_3679_);
    v___x_3685_ = lean_array_push(v___x_3684_, v___x_3678_);
    return v___x_3685_;
}
pub unsafe fn _init_l_Lean_Meta_eqnAffectingOptions() -> *mut crate::leanh::LeanObject {
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_eqnAffectingOptions___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_eqnAffectingOptions___closed__0_once),
        _init_l_Lean_Meta_eqnAffectingOptions___closed__0,
    );
    return v___x_3686_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(
    mut v_env_3687_: *mut crate::leanh::LeanObject,
    mut v_as_3688_: *mut crate::leanh::LeanObject,
    mut v_i_3689_: usize,
    mut v_stop_3690_: usize,
    mut v_b_3691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: usize = 0;
    let mut v___x_3695_: usize = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u8 = 0;
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3697_ = lean_usize_dec_eq(v_i_3689_, v_stop_3690_);
                if v___x_3697_ == 0 {
                    v___x_3698_ = lean_array_uget_borrowed(v_as_3688_, v_i_3689_);
                    v_fst_3699_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                    crate::leanh::lean_inc(v_fst_3699_);
                    crate::leanh::lean_inc_ref(v_env_3687_);
                    v___x_3700_ =
                        l_Lean_Environment_contains(v_env_3687_, v_fst_3699_, v___x_3697_);
                    if v___x_3700_ == 0 {
                        v___y_3693_ = v_b_3691_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_3698_);
                        v___x_3701_ = lean_array_push(v_b_3691_, v___x_3698_);
                        v___y_3693_ = v___x_3701_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3687_);
                    return v_b_3691_;
                }
            }
            1 => {
                v___x_3694_ = 1usize;
                v___x_3695_ = lean_usize_add(v_i_3689_, v___x_3694_);
                v_i_3689_ = v___x_3695_;
                v_b_3691_ = v___y_3693_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_3702_: *mut crate::leanh::LeanObject,
    mut v_as_3703_: *mut crate::leanh::LeanObject,
    mut v_i_3704_: *mut crate::leanh::LeanObject,
    mut v_stop_3705_: *mut crate::leanh::LeanObject,
    mut v_b_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3707_: usize = 0;
    let mut v_stop_boxed_3708_: usize = 0;
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3707_ = crate::leanh::lean_unbox_usize(v_i_3704_);
    crate::leanh::lean_dec(v_i_3704_);
    v_stop_boxed_3708_ = crate::leanh::lean_unbox_usize(v_stop_3705_);
    crate::leanh::lean_dec(v_stop_3705_);
    v_res_3709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_3702_, v_as_3703_, v_i_boxed_3707_, v_stop_boxed_3708_, v_b_3706_);
    crate::leanh::lean_dec_ref(v_as_3703_);
    return v_res_3709_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_3710_: *mut crate::leanh::LeanObject,
    mut v_x_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3711_) == 0 {
                    v_k_3712_ = crate::leanh::lean_ctor_get(v_x_3711_, 1);
                    v_v_3713_ = crate::leanh::lean_ctor_get(v_x_3711_, 2);
                    v_l_3714_ = crate::leanh::lean_ctor_get(v_x_3711_, 3);
                    v_r_3715_ = crate::leanh::lean_ctor_get(v_x_3711_, 4);
                    v___x_3716_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_3710_, v_l_3714_);
                    crate::leanh::lean_inc(v_v_3713_);
                    crate::leanh::lean_inc(v_k_3712_);
                    v___x_3717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_k_3712_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_v_3713_);
                    v___x_3718_ = lean_array_push(v___x_3716_, v___x_3717_);
                    v_init_3710_ = v___x_3718_;
                    v_x_3711_ = v_r_3715_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3710_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_3720_: *mut crate::leanh::LeanObject,
    mut v_x_3721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3722_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_3720_, v_x_3721_);
    crate::leanh::lean_dec(v_x_3721_);
    return v_res_3722_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(
    mut v_env_3729_: *mut crate::leanh::LeanObject,
    mut v_s_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    v___x_3731_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3732_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
    v___x_3733_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v___x_3732_, v_s_3730_);
    v___x_3734_ = lean_array_get_size(v___x_3733_);
    v___x_3735_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
    v___x_3736_ = lean_nat_dec_lt(v___x_3731_, v___x_3734_);
    if v___x_3736_ == 0 {
        let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3733_);
        crate::leanh::lean_dec_ref(v_env_3729_);
        v___x_3737_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
        return v___x_3737_;
    } else {
        let mut v___x_3738_: u8 = 0;
        v___x_3738_ = lean_nat_dec_le(v___x_3734_, v___x_3734_);
        if v___x_3738_ == 0 {
            if v___x_3736_ == 0 {
                let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_3733_);
                crate::leanh::lean_dec_ref(v_env_3729_);
                v___x_3739_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
                return v___x_3739_;
            } else {
                let mut v___x_3740_: usize = 0;
                let mut v___x_3741_: usize = 0;
                let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3740_ = 0usize;
                v___x_3741_ = lean_usize_of_nat(v___x_3734_);
                v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_3729_, v___x_3733_, v___x_3740_, v___x_3741_, v___x_3735_);
                crate::leanh::lean_dec_ref(v___x_3733_);
                crate::leanh::lean_inc_ref_n(v___x_3742_, 2);
                v___x_3743_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3743_, 0, v___x_3742_);
                crate::leanh::lean_ctor_set(v___x_3743_, 1, v___x_3742_);
                crate::leanh::lean_ctor_set(v___x_3743_, 2, v___x_3742_);
                return v___x_3743_;
            }
        } else {
            let mut v___x_3744_: usize = 0;
            let mut v___x_3745_: usize = 0;
            let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3744_ = 0usize;
            v___x_3745_ = lean_usize_of_nat(v___x_3734_);
            v___x_3746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__1(v_env_3729_, v___x_3733_, v___x_3744_, v___x_3745_, v___x_3735_);
            crate::leanh::lean_dec_ref(v___x_3733_);
            crate::leanh::lean_inc_ref_n(v___x_3746_, 2);
            v___x_3747_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3747_, 0, v___x_3746_);
            crate::leanh::lean_ctor_set(v___x_3747_, 1, v___x_3746_);
            crate::leanh::lean_ctor_set(v___x_3747_, 2, v___x_3746_);
            return v___x_3747_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(
    mut v_env_3748_: *mut crate::leanh::LeanObject,
    mut v_s_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_(v_env_3748_, v_s_3749_);
    crate::leanh::lean_dec(v_s_3749_);
    return v_res_3750_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3758_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
    v___x_3759_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_;
    v___x_3760_ = crate::leanh::lean_box(1);
    v___x_3761_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3759_, v___x_3760_, v___f_3758_);
    return v___x_3761_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2____boxed(
    mut v_a_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3763_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
    return v_res_3763_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(
    mut v_init_3764_: *mut crate::leanh::LeanObject,
    mut v_t_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0_spec__0(v_init_3764_, v_t_3765_);
    return v___x_3766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_3767_: *mut crate::leanh::LeanObject,
    mut v_t_3768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3769_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2__spec__0(v_init_3767_, v_t_3768_);
    crate::leanh::lean_dec(v_t_3768_);
    return v_res_3769_;
}
pub unsafe fn _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
    v___x_3777_ = lean_string_utf8_byte_size(v___x_3776_);
    return v___x_3777_;
}
pub unsafe fn l_Lean_Meta_isEqnReservedNameSuffix(
    mut v_s_3778_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: u8 = 0;
    v___x_3779_ = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
    v___x_3780_ = lean_string_utf8_byte_size(v_s_3778_);
    v___x_3781_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_isEqnReservedNameSuffix___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_isEqnReservedNameSuffix___closed__0_once),
        _init_l_Lean_Meta_isEqnReservedNameSuffix___closed__0,
    );
    v___x_3782_ = lean_nat_dec_le(v___x_3781_, v___x_3780_);
    if v___x_3782_ == 0 {
        crate::leanh::lean_dec_ref(v_s_3778_);
        return v___x_3782_;
    } else {
        let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3784_: u8 = 0;
        v___x_3783_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3784_ = lean_string_memcmp(
            v_s_3778_,
            v___x_3779_,
            v___x_3783_,
            v___x_3783_,
            v___x_3781_,
        );
        if v___x_3784_ == 0 {
            crate::leanh::lean_dec_ref(v_s_3778_);
            return v___x_3784_;
        } else {
            let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3789_: u8 = 0;
            v___x_3785_ = crate::leanh::lean_unsigned_to_nat(3);
            crate::leanh::lean_inc_ref(v_s_3778_);
            v___x_3786_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3786_, 0, v_s_3778_);
            crate::leanh::lean_ctor_set(v___x_3786_, 1, v___x_3783_);
            crate::leanh::lean_ctor_set(v___x_3786_, 2, v___x_3780_);
            v___x_3787_ = l_String_Slice_Pos_nextn(v___x_3786_, v___x_3783_, v___x_3785_);
            crate::leanh::lean_dec_ref_known(v___x_3786_, 3);
            v___x_3788_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3788_, 0, v_s_3778_);
            crate::leanh::lean_ctor_set(v___x_3788_, 1, v___x_3787_);
            crate::leanh::lean_ctor_set(v___x_3788_, 2, v___x_3780_);
            v___x_3789_ = l_String_Slice_isNat(v___x_3788_);
            crate::leanh::lean_dec_ref_known(v___x_3788_, 3);
            return v___x_3789_;
        }
    }
}
pub unsafe fn l_Lean_Meta_isEqnReservedNameSuffix___boxed(
    mut v_s_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: u8 = 0;
    let mut v_r_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_3790_);
    v_r_3792_ = crate::leanh::lean_box((v_res_3791_) as usize);
    return v_r_3792_;
}
pub unsafe fn l_Lean_Meta_isEqnLikeSuffix(mut v_s_3797_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_3799_: u8 = 0;
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3801_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                v___x_3802_ = lean_string_dec_eq(v_s_3797_, v___x_3801_);
                if v___x_3802_ == 0 {
                    v___x_3803_ = l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
                    v___x_3804_ = lean_string_dec_eq(v_s_3797_, v___x_3803_);
                    v___y_3799_ = v___x_3804_;
                    state = 1;
                    continue;
                } else {
                    v___y_3799_ = v___x_3802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3799_ == 0 {
                    v___x_3800_ = l_Lean_Meta_isEqnReservedNameSuffix(v_s_3797_);
                    return v___x_3800_;
                } else {
                    crate::leanh::lean_dec_ref(v_s_3797_);
                    return v___y_3799_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isEqnLikeSuffix___boxed(
    mut v_s_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3806_: u8 = 0;
    let mut v_r_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3806_ = l_Lean_Meta_isEqnLikeSuffix(v_s_3805_);
    v_r_3807_ = crate::leanh::lean_box((v_res_3806_) as usize);
    return v_r_3807_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(
    mut v_str_3811_: *mut crate::leanh::LeanObject,
    mut v_env_3812_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3813_: *mut crate::leanh::LeanObject,
    mut v_b_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: u8 = 0;
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3813_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_3812_);
                    crate::leanh::lean_dec_ref(v_str_3811_);
                    crate::leanh::lean_inc_ref(v_b_3814_);
                    return v_b_3814_;
                } else {
                    v_head_3815_ = crate::leanh::lean_ctor_get(v_as_x27_3813_, 0);
                    v_tail_3816_ = crate::leanh::lean_ctor_get(v_as_x27_3813_, 1);
                    v___x_3817_ = crate::leanh::lean_box(0);
                    v___x_3818_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0;
                    v___x_3826_ = 0;
                    crate::leanh::lean_inc_ref(v_env_3812_);
                    v___x_3827_ = l_Lean_Environment_setExporting(v_env_3812_, v___x_3826_);
                    crate::leanh::lean_inc(v_head_3815_);
                    v___x_3828_ = l_Lean_Environment_isSafeDefinition(v___x_3827_, v_head_3815_);
                    if v___x_3828_ == 0 {
                        v___y_3820_ = v___x_3828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_head_3815_);
                        crate::leanh::lean_inc_ref(v_env_3812_);
                        v___x_3829_ = lean_is_matcher(v_env_3812_, v_head_3815_);
                        if v___x_3829_ == 0 {
                            v___y_3820_ = v___x_3828_;
                            state = 1;
                            continue;
                        } else {
                            v_as_x27_3813_ = v_tail_3816_;
                            v_b_3814_ = v___x_3818_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_3820_ == 0 {
                    v_as_x27_3813_ = v_tail_3816_;
                    v_b_3814_ = v___x_3818_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_3812_);
                    crate::leanh::lean_inc(v_head_3815_);
                    v___x_3822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3822_, 0, v_head_3815_);
                    crate::leanh::lean_ctor_set(v___x_3822_, 1, v_str_3811_);
                    v___x_3823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3823_, 0, v___x_3822_);
                    v___x_3824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3824_, 0, v___x_3823_);
                    v___x_3825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3825_, 0, v___x_3824_);
                    crate::leanh::lean_ctor_set(v___x_3825_, 1, v___x_3817_);
                    return v___x_3825_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(
    mut v_str_3831_: *mut crate::leanh::LeanObject,
    mut v_env_3832_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3833_: *mut crate::leanh::LeanObject,
    mut v_b_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(
        v_str_3831_,
        v_env_3832_,
        v_as_x27_3833_,
        v_b_3834_,
    );
    crate::leanh::lean_dec_ref(v_b_3834_);
    crate::leanh::lean_dec(v_as_x27_3833_);
    return v_res_3835_;
}
pub unsafe fn l_Lean_Meta_declFromEqLikeName(
    mut v_env_3836_: *mut crate::leanh::LeanObject,
    mut v_name_3837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_name_3837_) == 1 {
        let mut v_pre_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3840_: u8 = 0;
        v_pre_3838_ = crate::leanh::lean_ctor_get(v_name_3837_, 0);
        crate::leanh::lean_inc(v_pre_3838_);
        v_str_3839_ = crate::leanh::lean_ctor_get(v_name_3837_, 1);
        crate::leanh::lean_inc_ref_n(v_str_3839_, 2);
        crate::leanh::lean_dec_ref_known(v_name_3837_, 2);
        v___x_3840_ = l_Lean_Meta_isEqnLikeSuffix(v_str_3839_);
        if v___x_3840_ == 0 {
            let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_str_3839_);
            crate::leanh::lean_dec(v_pre_3838_);
            crate::leanh::lean_dec_ref(v_env_3836_);
            v___x_3841_ = crate::leanh::lean_box(0);
            return v___x_3841_;
        } else {
            let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_pre_3838_);
            v___x_3842_ = l_Lean_privateToUserName(v_pre_3838_);
            v___x_3843_ = crate::leanh::lean_box(0);
            v___x_3844_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3842_);
            crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
            v___x_3845_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3845_, 0, v_pre_3838_);
            crate::leanh::lean_ctor_set(v___x_3845_, 1, v___x_3844_);
            v___x_3846_ = crate::leanh::lean_box(0);
            v___x_3847_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg___closed__0;
            v___x_3848_ =
                l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(
                    v_str_3839_,
                    v_env_3836_,
                    v___x_3845_,
                    v___x_3847_,
                );
            crate::leanh::lean_dec_ref_known(v___x_3845_, 2);
            v_fst_3849_ = crate::leanh::lean_ctor_get(v___x_3848_, 0);
            crate::leanh::lean_inc(v_fst_3849_);
            crate::leanh::lean_dec_ref(v___x_3848_);
            if crate::leanh::lean_obj_tag(v_fst_3849_) == 0 {
                return v___x_3846_;
            } else {
                let mut v_val_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_val_3850_ = crate::leanh::lean_ctor_get(v_fst_3849_, 0);
                crate::leanh::lean_inc(v_val_3850_);
                crate::leanh::lean_dec_ref_known(v_fst_3849_, 1);
                return v_val_3850_;
            }
        }
    } else {
        let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_name_3837_);
        crate::leanh::lean_dec_ref(v_env_3836_);
        v___x_3851_ = crate::leanh::lean_box(0);
        return v___x_3851_;
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(
    mut v_str_3852_: *mut crate::leanh::LeanObject,
    mut v_env_3853_: *mut crate::leanh::LeanObject,
    mut v_as_3854_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3855_: *mut crate::leanh::LeanObject,
    mut v_b_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___redArg(
        v_str_3852_,
        v_env_3853_,
        v_as_x27_3855_,
        v_b_3856_,
    );
    return v___x_3858_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0___boxed(
    mut v_str_3859_: *mut crate::leanh::LeanObject,
    mut v_env_3860_: *mut crate::leanh::LeanObject,
    mut v_as_3861_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3862_: *mut crate::leanh::LeanObject,
    mut v_b_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3865_ = l_List_forIn_x27_loop___at___00Lean_Meta_declFromEqLikeName_spec__0(
        v_str_3859_,
        v_env_3860_,
        v_as_3861_,
        v_as_x27_3862_,
        v_b_3863_,
        v_a_3864_,
    );
    crate::leanh::lean_dec_ref(v_b_3863_);
    crate::leanh::lean_dec(v_as_x27_3862_);
    crate::leanh::lean_dec(v_as_3861_);
    return v_res_3865_;
}
pub unsafe fn l_Lean_Meta_mkEqLikeNameFor(
    mut v_env_3866_: *mut crate::leanh::LeanObject,
    mut v_declName_3867_: *mut crate::leanh::LeanObject,
    mut v_suffix_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_3873_: u8 = 0;
    let mut v_name_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: u8 = 0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v_name_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3872_ = l_Lean_Environment_header(v_env_3866_);
                v_isModule_3873_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3872_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_3872_);
                if v_isModule_3873_ == 0 {
                    crate::leanh::lean_dec_ref(v_env_3866_);
                    v_name_3874_ = l_Lean_Name_str___override(v_declName_3867_, v_suffix_3868_);
                    return v_name_3874_;
                } else {
                    v___x_3875_ = 0;
                    crate::leanh::lean_inc_ref(v_env_3866_);
                    v___x_3876_ = l_Lean_Environment_setExporting(v_env_3866_, v_isModule_3873_);
                    crate::leanh::lean_inc(v_declName_3867_);
                    v___x_3877_ =
                        l_Lean_Environment_find_x3f(v___x_3876_, v_declName_3867_, v___x_3875_);
                    if crate::leanh::lean_obj_tag(v___x_3877_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_3878_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                        crate::leanh::lean_inc(v_val_3878_);
                        crate::leanh::lean_dec_ref_known(v___x_3877_, 1);
                        v___x_3879_ = l_Lean_ConstantInfo_hasValue(v_val_3878_, v___x_3875_);
                        crate::leanh::lean_dec(v_val_3878_);
                        if v___x_3879_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_env_3866_);
                            v_name_3880_ =
                                l_Lean_Name_str___override(v_declName_3867_, v_suffix_3868_);
                            return v_name_3880_;
                        }
                    }
                }
            }
            1 => {
                v_name_3870_ = l_Lean_Name_str___override(v_declName_3867_, v_suffix_3868_);
                v___x_3871_ = l_Lean_mkPrivateName(v_env_3866_, v_name_3870_);
                crate::leanh::lean_dec_ref(v_env_3866_);
                return v___x_3871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3881_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3881_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__0);
    v___x_3883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3883_, 0, v___x_3882_);
    return v___x_3883_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
    v___x_3885_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3886_, 0, v___x_3885_);
    crate::leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
    crate::leanh::lean_ctor_set(v___x_3886_, 2, v___x_3885_);
    crate::leanh::lean_ctor_set(v___x_3886_, 3, v___x_3885_);
    crate::leanh::lean_ctor_set(v___x_3886_, 4, v___x_3884_);
    crate::leanh::lean_ctor_set(v___x_3886_, 5, v___x_3884_);
    crate::leanh::lean_ctor_set(v___x_3886_, 6, v___x_3884_);
    crate::leanh::lean_ctor_set(v___x_3886_, 7, v___x_3884_);
    crate::leanh::lean_ctor_set(v___x_3886_, 8, v___x_3884_);
    crate::leanh::lean_ctor_set(v___x_3886_, 9, v___x_3884_);
    return v___x_3886_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3888_ = lean_mk_empty_array_with_capacity(v___x_3887_);
    v___x_3889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3889_, 0, v___x_3888_);
    return v___x_3889_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: usize = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = 5usize;
    v___x_3891_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3892_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3893_ = lean_mk_empty_array_with_capacity(v___x_3892_);
    v___x_3894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__3);
    v___x_3895_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3895_, 0, v___x_3894_);
    crate::leanh::lean_ctor_set(v___x_3895_, 1, v___x_3893_);
    crate::leanh::lean_ctor_set(v___x_3895_, 2, v___x_3891_);
    crate::leanh::lean_ctor_set(v___x_3895_, 3, v___x_3891_);
    crate::leanh::lean_ctor_set_usize(v___x_3895_, 4, v___x_3890_);
    return v___x_3895_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = crate::leanh::lean_box(1);
    v___x_3897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
    v___x_3898_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__1);
    v___x_3899_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3899_, 0, v___x_3898_);
    crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3897_);
    crate::leanh::lean_ctor_set(v___x_3899_, 2, v___x_3896_);
    return v___x_3899_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(
    mut v_msgData_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = lean_st_ref_get(v___y_3902_);
    v_env_3905_ = crate::leanh::lean_ctor_get(v___x_3904_, 0);
    crate::leanh::lean_inc_ref(v_env_3905_);
    crate::leanh::lean_dec(v___x_3904_);
    v_options_3906_ = crate::leanh::lean_ctor_get(v___y_3901_, 2);
    v___x_3907_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__2);
    v___x_3908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_3906_);
    v___x_3909_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3909_, 0, v_env_3905_);
    crate::leanh::lean_ctor_set(v___x_3909_, 1, v___x_3907_);
    crate::leanh::lean_ctor_set(v___x_3909_, 2, v___x_3908_);
    crate::leanh::lean_ctor_set(v___x_3909_, 3, v_options_3906_);
    v___x_3910_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3910_, 0, v___x_3909_);
    crate::leanh::lean_ctor_set(v___x_3910_, 1, v_msgData_3900_);
    v___x_3911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3911_, 0, v___x_3910_);
    return v___x_3911_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3916_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msgData_3912_, v___y_3913_, v___y_3914_);
    crate::leanh::lean_dec(v___y_3914_);
    crate::leanh::lean_dec_ref(v___y_3913_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(
    mut v_msg_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3921_ = crate::leanh::lean_ctor_get(v___y_3918_, 5);
                v___x_3922_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_3917_, v___y_3918_, v___y_3919_);
                v_a_3923_ = crate::leanh::lean_ctor_get(v___x_3922_, 0);
                v_isSharedCheck_3931_ = (!crate::leanh::lean_is_exclusive(v___x_3922_)) as u8;
                if v_isSharedCheck_3931_ == 0 {
                    v___x_3925_ = v___x_3922_;
                    v_isShared_3926_ = v_isSharedCheck_3931_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3923_);
                    crate::leanh::lean_dec(v___x_3922_);
                    v___x_3925_ = crate::leanh::lean_box(0);
                    v_isShared_3926_ = v_isSharedCheck_3931_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3921_);
                v___x_3927_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3927_, 0, v_ref_3921_);
                crate::leanh::lean_ctor_set(v___x_3927_, 1, v_a_3923_);
                if v_isShared_3926_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3925_, 1);
                    crate::leanh::lean_ctor_set(v___x_3925_, 0, v___x_3927_);
                    v___x_3929_ = v___x_3925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_msg_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_3932_, v___y_3933_, v___y_3934_);
    crate::leanh::lean_dec(v___y_3934_);
    crate::leanh::lean_dec_ref(v___y_3933_);
    return v_res_3936_;
}
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3938_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0;
    v___x_3939_ = l_Lean_stringToMessageData(v___x_3938_);
    return v___x_3939_;
}
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3941_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2;
    v___x_3942_ = l_Lean_stringToMessageData(v___x_3941_);
    return v___x_3942_;
}
pub unsafe fn _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4;
    v___x_3945_ = l_Lean_stringToMessageData(v___x_3944_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(
    mut v_declName_3946_: *mut crate::leanh::LeanObject,
    mut v_reservedName_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: u8 = 0;
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1_once), _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
    v___x_3952_ = 0;
    v___x_3953_ = l_Lean_MessageData_ofConstName(v_declName_3946_, v___x_3952_);
    v___x_3954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3951_);
    crate::leanh::lean_ctor_set(v___x_3954_, 1, v___x_3953_);
    v___x_3955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3_once), _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
    v___x_3956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3954_);
    crate::leanh::lean_ctor_set(v___x_3956_, 1, v___x_3955_);
    v___x_3957_ = 1;
    v___x_3958_ = l_Lean_MessageData_ofConstName(v_reservedName_3947_, v___x_3957_);
    v___x_3959_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3959_, 0, v___x_3956_);
    crate::leanh::lean_ctor_set(v___x_3959_, 1, v___x_3958_);
    v___x_3960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5_once), _init_l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
    v___x_3961_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3961_, 0, v___x_3959_);
    crate::leanh::lean_ctor_set(v___x_3961_, 1, v___x_3960_);
    v___x_3962_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v___x_3961_, v___y_3948_, v___y_3949_);
    return v___x_3962_;
}
pub unsafe fn l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(
    mut v_declName_3963_: *mut crate::leanh::LeanObject,
    mut v_reservedName_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3968_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_3963_, v_reservedName_3964_, v___y_3965_, v___y_3966_);
    crate::leanh::lean_dec(v___y_3966_);
    crate::leanh::lean_dec_ref(v___y_3965_);
    return v_res_3968_;
}
pub unsafe fn l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(
    mut v_declName_3969_: *mut crate::leanh::LeanObject,
    mut v_suffix_3970_: *mut crate::leanh::LeanObject,
    mut v___y_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reservedName_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: u8 = 0;
    v___x_3974_ = lean_st_ref_get(v___y_3972_);
    v_env_3975_ = crate::leanh::lean_ctor_get(v___x_3974_, 0);
    crate::leanh::lean_inc_ref(v_env_3975_);
    crate::leanh::lean_dec(v___x_3974_);
    crate::leanh::lean_inc(v_declName_3969_);
    v_reservedName_3976_ = l_Lean_Name_str___override(v_declName_3969_, v_suffix_3970_);
    v___x_3977_ = 1;
    crate::leanh::lean_inc(v_reservedName_3976_);
    v___x_3978_ = l_Lean_Environment_contains(v_env_3975_, v_reservedName_3976_, v___x_3977_);
    if v___x_3978_ == 0 {
        let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_reservedName_3976_);
        crate::leanh::lean_dec(v_declName_3969_);
        v___x_3979_ = crate::leanh::lean_box(0);
        v___x_3980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
        return v___x_3980_;
    } else {
        let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3981_ = l_Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(v_declName_3969_, v_reservedName_3976_, v___y_3971_, v___y_3972_);
        return v___x_3981_;
    }
}
pub unsafe fn l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(
    mut v_declName_3982_: *mut crate::leanh::LeanObject,
    mut v_suffix_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_3982_, v_suffix_3983_, v___y_3984_, v___y_3985_);
    crate::leanh::lean_dec(v___y_3985_);
    crate::leanh::lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_Meta_ensureEqnReservedNamesAvailable(
    mut v_declName_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
    crate::leanh::lean_inc(v_declName_3988_);
    v___x_3993_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_3988_, v___x_3992_, v_a_3989_, v_a_3990_);
    if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
        let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3993_, 1);
        v___x_3994_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
        crate::leanh::lean_inc(v_declName_3988_);
        v___x_3995_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_3988_, v___x_3994_, v_a_3989_, v_a_3990_);
        if crate::leanh::lean_obj_tag(v___x_3995_) == 0 {
            let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3995_, 1);
            v___x_3996_ = l_Lean_Meta_eqn1ThmSuffix___closed__0;
            v___x_3997_ = l_Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(v_declName_3988_, v___x_3996_, v_a_3989_, v_a_3990_);
            return v___x_3997_;
        } else {
            crate::leanh::lean_dec(v_declName_3988_);
            return v___x_3995_;
        }
    } else {
        crate::leanh::lean_dec(v_declName_3988_);
        return v___x_3993_;
    }
}
pub unsafe fn l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(
    mut v_declName_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4002_ =
        l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3998_, v_a_3999_, v_a_4000_);
    crate::leanh::lean_dec(v_a_4000_);
    crate::leanh::lean_dec_ref(v_a_3999_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4003_: *mut crate::leanh::LeanObject,
    mut v_msg_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___redArg(v_msg_4004_, v___y_4005_, v___y_4006_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4009_: *mut crate::leanh::LeanObject,
    mut v_msg_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4014_ = l_Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1(v_00_u03b1_4009_, v_msg_4010_, v___y_4011_, v___y_4012_);
    crate::leanh::lean_dec(v___y_4012_);
    crate::leanh::lean_dec_ref(v___y_4011_);
    return v_res_4014_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(
    mut v_env_4015_: *mut crate::leanh::LeanObject,
    mut v_n_4016_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_4016_);
    crate::leanh::lean_inc_ref(v_env_4015_);
    v___x_4017_ = l_Lean_Meta_declFromEqLikeName(v_env_4015_, v_n_4016_);
    if crate::leanh::lean_obj_tag(v___x_4017_) == 1 {
        let mut v_val_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: u8 = 0;
        v_val_4018_ = crate::leanh::lean_ctor_get(v___x_4017_, 0);
        crate::leanh::lean_inc(v_val_4018_);
        crate::leanh::lean_dec_ref_known(v___x_4017_, 1);
        v_fst_4019_ = crate::leanh::lean_ctor_get(v_val_4018_, 0);
        crate::leanh::lean_inc(v_fst_4019_);
        v_snd_4020_ = crate::leanh::lean_ctor_get(v_val_4018_, 1);
        crate::leanh::lean_inc(v_snd_4020_);
        crate::leanh::lean_dec(v_val_4018_);
        v___x_4021_ = l_Lean_Meta_mkEqLikeNameFor(v_env_4015_, v_fst_4019_, v_snd_4020_);
        v___x_4022_ = lean_name_eq(v_n_4016_, v___x_4021_);
        crate::leanh::lean_dec(v___x_4021_);
        crate::leanh::lean_dec(v_n_4016_);
        return v___x_4022_;
    } else {
        let mut v___x_4023_: u8 = 0;
        crate::leanh::lean_dec(v___x_4017_);
        crate::leanh::lean_dec(v_n_4016_);
        crate::leanh::lean_dec_ref(v_env_4015_);
        v___x_4023_ = 0;
        return v___x_4023_;
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(
    mut v_env_4024_: *mut crate::leanh::LeanObject,
    mut v_n_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4026_: u8 = 0;
    let mut v_r_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4026_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_(v_env_4024_, v_n_4025_);
    v_r_4027_ = crate::leanh::lean_box((v_res_4026_) as usize);
    return v_r_4027_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4030_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_;
    v___x_4031_ = l_Lean_registerReservedNamePredicate(v___f_4030_);
    return v___x_4031_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2____boxed(
    mut v_a_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4033_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
    return v_res_4033_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = crate::leanh::lean_box(0);
    v___x_4036_ = lean_st_mk_ref(v___x_4035_);
    v___x_4037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4036_);
    return v___x_4037_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2____boxed(
    mut v_a_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
    return v_res_4039_;
}
pub unsafe fn _init_l_Lean_Meta_registerGetEqnsFn___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = l_Lean_Meta_registerGetEqnsFn___closed__0;
    v___x_4042_ = lean_mk_io_user_error(v___x_4041_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_Meta_registerGetEqnsFn(
    mut v_f_4043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4062_: u8 = 0;
    let mut v_a_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4045_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_4045_) == 0 {
                    v_a_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_isSharedCheck_4062_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4062_ == 0 {
                        v___x_4048_ = v___x_4045_;
                        v_isShared_4049_ = v_isSharedCheck_4062_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4046_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4048_ = crate::leanh::lean_box(0);
                        v_isShared_4049_ = v_isSharedCheck_4062_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4043_);
                    v_a_4063_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_isSharedCheck_4070_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4070_ == 0 {
                        v___x_4065_ = v___x_4045_;
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4063_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4065_ = crate::leanh::lean_box(0);
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4050_ = (crate::leanh::lean_unbox(v_a_4046_) as u8);
                crate::leanh::lean_dec(v_a_4046_);
                if v___x_4050_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_4043_);
                    v___x_4051_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerGetEqnsFn___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerGetEqnsFn___closed__1_once),
                        _init_l_Lean_Meta_registerGetEqnsFn___closed__1,
                    );
                    if v_isShared_4049_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4048_, 1);
                        crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4051_);
                        v___x_4053_ = v___x_4048_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
                        v___x_4053_ = v_reuseFailAlloc_4054_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4055_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
                    v___x_4056_ = lean_st_ref_take(v___x_4055_);
                    v___x_4057_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4057_, 0, v_f_4043_);
                    crate::leanh::lean_ctor_set(v___x_4057_, 1, v___x_4056_);
                    v___x_4058_ = lean_st_ref_set(v___x_4055_, v___x_4057_);
                    if v_isShared_4049_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4058_);
                        v___x_4060_ = v___x_4048_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
                        v___x_4060_ = v_reuseFailAlloc_4061_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4053_;
            }
            3 => {
                return v___x_4060_;
            }
            4 => {
                if v_isShared_4066_ == 0 {
                    v___x_4068_ = v___x_4065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_registerGetEqnsFn___boxed(
    mut v_f_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4073_ = l_Lean_Meta_registerGetEqnsFn(v_f_4071_);
    return v_res_4073_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(
    mut v_declName_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
    mut v_a_4077_: *mut crate::leanh::LeanObject,
    mut v_a_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: u8 = 0;
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_kind_4092_: u8 = 0;
    let mut v_sig_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4084_ = lean_st_ref_get(v_a_4078_);
                v_env_4085_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                crate::leanh::lean_inc_ref(v_env_4085_);
                crate::leanh::lean_dec(v___x_4084_);
                v___x_4086_ = 0;
                crate::leanh::lean_inc(v_declName_4074_);
                v___x_4087_ =
                    l_Lean_Environment_findAsync_x3f(v_env_4085_, v_declName_4074_, v___x_4086_);
                if crate::leanh::lean_obj_tag(v___x_4087_) == 1 {
                    v_val_4088_ = crate::leanh::lean_ctor_get(v___x_4087_, 0);
                    v_isSharedCheck_4119_ = (!crate::leanh::lean_is_exclusive(v___x_4087_)) as u8;
                    if v_isSharedCheck_4119_ == 0 {
                        v___x_4090_ = v___x_4087_;
                        v_isShared_4091_ = v_isSharedCheck_4119_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4088_);
                        crate::leanh::lean_dec(v___x_4087_);
                        v___x_4090_ = crate::leanh::lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4119_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4087_);
                    crate::leanh::lean_dec(v_declName_4074_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4081_ = 0;
                v___x_4082_ = crate::leanh::lean_box((v___x_4081_) as usize);
                v___x_4083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4083_, 0, v___x_4082_);
                return v___x_4083_;
            }
            2 => {
                v_kind_4092_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_4088_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_kind_4092_ == 0 {
                    v_sig_4093_ = crate::leanh::lean_ctor_get(v_val_4088_, 1);
                    crate::leanh::lean_inc_ref(v_sig_4093_);
                    crate::leanh::lean_dec(v_val_4088_);
                    v___x_4094_ = lean_st_ref_get(v_a_4078_);
                    v_env_4095_ = crate::leanh::lean_ctor_get(v___x_4094_, 0);
                    crate::leanh::lean_inc_ref(v_env_4095_);
                    crate::leanh::lean_dec(v___x_4094_);
                    v___x_4096_ = lean_is_matcher(v_env_4095_, v_declName_4074_);
                    if v___x_4096_ == 0 {
                        crate::leanh::lean_del_object(v___x_4090_);
                        v___x_4097_ = lean_task_get_own(v_sig_4093_);
                        v_type_4098_ = crate::leanh::lean_ctor_get(v___x_4097_, 2);
                        crate::leanh::lean_inc_ref(v_type_4098_);
                        crate::leanh::lean_dec(v___x_4097_);
                        v___x_4099_ = l_Lean_Meta_isProp(
                            v_type_4098_,
                            v_a_4075_,
                            v_a_4076_,
                            v_a_4077_,
                            v_a_4078_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4099_) == 0 {
                            v_a_4100_ = crate::leanh::lean_ctor_get(v___x_4099_, 0);
                            v_isSharedCheck_4114_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4099_)) as u8;
                            if v_isSharedCheck_4114_ == 0 {
                                v___x_4102_ = v___x_4099_;
                                v_isShared_4103_ = v_isSharedCheck_4114_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4100_);
                                crate::leanh::lean_dec(v___x_4099_);
                                v___x_4102_ = crate::leanh::lean_box(0);
                                v_isShared_4103_ = v_isSharedCheck_4114_;
                                state = 3;
                                continue;
                            }
                        } else {
                            return v___x_4099_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_sig_4093_);
                        v___x_4115_ = crate::leanh::lean_box((v___x_4086_) as usize);
                        if v_isShared_4091_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4090_, 0);
                            crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4115_);
                            v___x_4117_ = v___x_4090_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4118_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v___x_4115_);
                            v___x_4117_ = v_reuseFailAlloc_4118_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4090_);
                    crate::leanh::lean_dec(v_val_4088_);
                    crate::leanh::lean_dec(v_declName_4074_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4104_ = (crate::leanh::lean_unbox(v_a_4100_) as u8);
                crate::leanh::lean_dec(v_a_4100_);
                if v___x_4104_ == 0 {
                    v___x_4105_ = 1;
                    v___x_4106_ = crate::leanh::lean_box((v___x_4105_) as usize);
                    if v_isShared_4103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4102_, 0, v___x_4106_);
                        v___x_4108_ = v___x_4102_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4109_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
                        v___x_4108_ = v_reuseFailAlloc_4109_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_4110_ = crate::leanh::lean_box((v___x_4096_) as usize);
                    if v_isShared_4103_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4102_, 0, v___x_4110_);
                        v___x_4112_ = v___x_4102_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
                        v___x_4112_ = v_reuseFailAlloc_4113_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4108_;
            }
            5 => {
                return v___x_4112_;
            }
            6 => {
                return v___x_4117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms___boxed(
    mut v_declName_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
    mut v_a_4123_: *mut crate::leanh::LeanObject,
    mut v_a_4124_: *mut crate::leanh::LeanObject,
    mut v_a_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4126_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(
        v_declName_4120_,
        v_a_4121_,
        v_a_4122_,
        v_a_4123_,
        v_a_4124_,
    );
    crate::leanh::lean_dec(v_a_4124_);
    crate::leanh::lean_dec_ref(v_a_4123_);
    crate::leanh::lean_dec(v_a_4122_);
    crate::leanh::lean_dec_ref(v_a_4121_);
    return v_res_4126_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4127_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__0,
    );
    v___x_4129_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4129_, 0, v___x_4128_);
    return v___x_4129_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEqnsExtState_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4130_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1,
    );
    return v___x_4130_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedEqnsExtState() -> *mut crate::leanh::LeanObject {
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
    return v___x_4131_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(
    mut v___x_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4132_);
    return v___x_4134_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(
    mut v___x_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4137_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_(v___x_4135_);
    return v_res_4137_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedEqnsExtState_default___closed__1,
    );
    v___f_4139_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_4139_, 0, v___x_4138_);
    return v___f_4139_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_);
    v___x_4142_ = crate::leanh::lean_box(0);
    v___x_4143_ = crate::leanh::lean_box(1);
    v___x_4144_ = l_Lean_registerEnvExtension___redArg(v___f_4141_, v___x_4142_, v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2____boxed(
    mut v_a_4145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
    return v_res_4146_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
    mut v_opts_4147_: *mut crate::leanh::LeanObject,
    mut v_opt_4148_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4149_ = crate::leanh::lean_ctor_get(v_opt_4148_, 0);
    v_defValue_4150_ = crate::leanh::lean_ctor_get(v_opt_4148_, 1);
    v_map_4151_ = crate::leanh::lean_ctor_get(v_opts_4147_, 0);
    v___x_4152_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4151_,
            v_name_4149_,
        );
    if crate::leanh::lean_obj_tag(v___x_4152_) == 0 {
        let mut v___x_4153_: u8 = 0;
        v___x_4153_ = (crate::leanh::lean_unbox(v_defValue_4150_) as u8);
        return v___x_4153_;
    } else {
        let mut v_val_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4154_ = crate::leanh::lean_ctor_get(v___x_4152_, 0);
        crate::leanh::lean_inc(v_val_4154_);
        crate::leanh::lean_dec_ref_known(v___x_4152_, 1);
        if crate::leanh::lean_obj_tag(v_val_4154_) == 1 {
            let mut v_v_4155_: u8 = 0;
            v_v_4155_ = crate::leanh::lean_ctor_get_uint8(v_val_4154_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4154_, 0);
            return v_v_4155_;
        } else {
            let mut v___x_4156_: u8 = 0;
            crate::leanh::lean_dec(v_val_4154_);
            v___x_4156_ = (crate::leanh::lean_unbox(v_defValue_4150_) as u8);
            return v___x_4156_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1___boxed(
    mut v_opts_4157_: *mut crate::leanh::LeanObject,
    mut v_opt_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4159_: u8 = 0;
    let mut v_r_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ =
        l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(v_opts_4157_, v_opt_4158_);
    crate::leanh::lean_dec_ref(v_opt_4158_);
    crate::leanh::lean_dec_ref(v_opts_4157_);
    v_r_4160_ = crate::leanh::lean_box((v_res_4159_) as usize);
    return v_r_4160_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(
    mut v_opts_4161_: *mut crate::leanh::LeanObject,
    mut v_opt_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4163_ = crate::leanh::lean_ctor_get(v_opt_4162_, 0);
    v_defValue_4164_ = crate::leanh::lean_ctor_get(v_opt_4162_, 1);
    v_map_4165_ = crate::leanh::lean_ctor_get(v_opts_4161_, 0);
    v___x_4166_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4165_,
            v_name_4163_,
        );
    if crate::leanh::lean_obj_tag(v___x_4166_) == 0 {
        crate::leanh::lean_inc(v_defValue_4164_);
        return v_defValue_4164_;
    } else {
        let mut v_val_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4167_ = crate::leanh::lean_ctor_get(v___x_4166_, 0);
        crate::leanh::lean_inc(v_val_4167_);
        crate::leanh::lean_dec_ref_known(v___x_4166_, 1);
        if crate::leanh::lean_obj_tag(v_val_4167_) == 3 {
            let mut v_v_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_4168_ = crate::leanh::lean_ctor_get(v_val_4167_, 0);
            crate::leanh::lean_inc(v_v_4168_);
            crate::leanh::lean_dec_ref_known(v_val_4167_, 1);
            return v_v_4168_;
        } else {
            crate::leanh::lean_dec(v_val_4167_);
            crate::leanh::lean_inc(v_defValue_4164_);
            return v_defValue_4164_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2___boxed(
    mut v_opts_4169_: *mut crate::leanh::LeanObject,
    mut v_opt_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ =
        l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(v_opts_4169_, v_opt_4170_);
    crate::leanh::lean_dec_ref(v_opt_4170_);
    crate::leanh::lean_dec_ref(v_opts_4169_);
    return v_res_4171_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(
    mut v_as_4175_: *mut crate::leanh::LeanObject,
    mut v_sz_4176_: usize,
    mut v_i_4177_: usize,
    mut v_b_4178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: usize = 0;
    let mut v___x_4182_: usize = 0;
    let mut v___x_4184_: u8 = 0;
    let mut v_a_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4189_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4184_ = lean_usize_dec_lt(v_i_4177_, v_sz_4176_);
                if v___x_4184_ == 0 {
                    return v_b_4178_;
                } else {
                    v_a_4185_ = lean_array_uget_borrowed(v_as_4175_, v_i_4177_);
                    v_fst_4186_ = crate::leanh::lean_ctor_get(v_a_4185_, 0);
                    v_snd_4187_ = crate::leanh::lean_ctor_get(v_a_4185_, 1);
                    v_map_4188_ = crate::leanh::lean_ctor_get(v_b_4178_, 0);
                    v_hasTrace_4189_ = crate::leanh::lean_ctor_get_uint8(
                        v_b_4178_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_isSharedCheck_4202_ = (!crate::leanh::lean_is_exclusive(v_b_4178_)) as u8;
                    if v_isSharedCheck_4202_ == 0 {
                        v___x_4191_ = v_b_4178_;
                        v_isShared_4192_ = v_isSharedCheck_4202_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_4188_);
                        crate::leanh::lean_dec(v_b_4178_);
                        v___x_4191_ = crate::leanh::lean_box(0);
                        v_isShared_4192_ = v_isSharedCheck_4202_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4181_ = 1usize;
                v___x_4182_ = lean_usize_add(v_i_4177_, v___x_4181_);
                v_i_4177_ = v___x_4182_;
                v_b_4178_ = v_a_4180_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v_snd_4187_);
                crate::leanh::lean_inc(v_fst_4186_);
                v___x_4193_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_4186_, v_snd_4187_, v_map_4188_);
                if v_hasTrace_4189_ == 0 {
                    v___x_4194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1;
                    v___x_4195_ = l_Lean_Name_isPrefixOf(v___x_4194_, v_fst_4186_);
                    if v_isShared_4192_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4191_, 0, v___x_4193_);
                        v___x_4197_ = v___x_4191_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4198_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4193_);
                        v___x_4197_ = v_reuseFailAlloc_4198_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_4192_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4191_, 0, v___x_4193_);
                        v___x_4200_ = v___x_4191_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4201_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4193_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4201_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4189_,
                        );
                        v___x_4200_ = v_reuseFailAlloc_4201_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4197_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4195_,
                );
                v_a_4180_ = v___x_4197_;
                state = 1;
                continue;
            }
            4 => {
                v_a_4180_ = v___x_4200_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___boxed(
    mut v_as_4203_: *mut crate::leanh::LeanObject,
    mut v_sz_4204_: *mut crate::leanh::LeanObject,
    mut v_i_4205_: *mut crate::leanh::LeanObject,
    mut v_b_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4207_: usize = 0;
    let mut v_i_boxed_4208_: usize = 0;
    let mut v_res_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4207_ = crate::leanh::lean_unbox_usize(v_sz_4204_);
    crate::leanh::lean_dec(v_sz_4204_);
    v_i_boxed_4208_ = crate::leanh::lean_unbox_usize(v_i_4205_);
    crate::leanh::lean_dec(v_i_4205_);
    v_res_4209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_as_4203_, v_sz_boxed_4207_, v_i_boxed_4208_, v_b_4206_);
    crate::leanh::lean_dec_ref(v_as_4203_);
    return v_res_4209_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(
    mut v_o_4210_: *mut crate::leanh::LeanObject,
    mut v_k_4211_: *mut crate::leanh::LeanObject,
    mut v_v_4212_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4214_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4213_ = crate::leanh::lean_ctor_get(v_o_4210_, 0);
                v_hasTrace_4214_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_4210_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4228_ = (!crate::leanh::lean_is_exclusive(v_o_4210_)) as u8;
                if v_isSharedCheck_4228_ == 0 {
                    v___x_4216_ = v_o_4210_;
                    v_isShared_4217_ = v_isSharedCheck_4228_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_4213_);
                    crate::leanh::lean_dec(v_o_4210_);
                    v___x_4216_ = crate::leanh::lean_box(0);
                    v_isShared_4217_ = v_isSharedCheck_4228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4218_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_4218_, 0 as u32, v_v_4212_);
                crate::leanh::lean_inc(v_k_4211_);
                v___x_4219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4211_, v___x_4218_, v_map_4213_);
                if v_hasTrace_4214_ == 0 {
                    v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1;
                    v___x_4221_ = l_Lean_Name_isPrefixOf(v___x_4220_, v_k_4211_);
                    crate::leanh::lean_dec(v_k_4211_);
                    if v_isShared_4217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4219_);
                        v___x_4223_ = v___x_4216_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4224_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4219_);
                        v___x_4223_ = v_reuseFailAlloc_4224_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_4211_);
                    if v_isShared_4217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4216_, 0, v___x_4219_);
                        v___x_4226_ = v___x_4216_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4219_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4227_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4214_,
                        );
                        v___x_4226_ = v_reuseFailAlloc_4227_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4221_,
                );
                return v___x_4223_;
            }
            3 => {
                return v___x_4226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0___boxed(
    mut v_o_4229_: *mut crate::leanh::LeanObject,
    mut v_k_4230_: *mut crate::leanh::LeanObject,
    mut v_v_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_4232_: u8 = 0;
    let mut v_res_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4232_ = (crate::leanh::lean_unbox(v_v_4231_) as u8);
    v_res_4233_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_o_4229_, v_k_4230_, v_v_boxed_4232_);
    return v_res_4233_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(
    mut v_opts_4234_: *mut crate::leanh::LeanObject,
    mut v_opt_4235_: *mut crate::leanh::LeanObject,
    mut v_val_4236_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4237_ = crate::leanh::lean_ctor_get(v_opt_4235_, 0);
    crate::leanh::lean_inc(v_name_4237_);
    crate::leanh::lean_dec_ref(v_opt_4235_);
    v___x_4238_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0_spec__0(v_opts_4234_, v_name_4237_, v_val_4236_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0___boxed(
    mut v_opts_4239_: *mut crate::leanh::LeanObject,
    mut v_opt_4240_: *mut crate::leanh::LeanObject,
    mut v_val_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_boxed_4242_: u8 = 0;
    let mut v_res_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4242_ = (crate::leanh::lean_unbox(v_val_4241_) as u8);
    v_res_4243_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(
        v_opts_4239_,
        v_opt_4240_,
        v_val_boxed_4242_,
    );
    return v_res_4243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(
    mut v_as_4244_: *mut crate::leanh::LeanObject,
    mut v_i_4245_: usize,
    mut v_stop_4246_: usize,
    mut v_b_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4248_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: usize = 0;
    let mut v___x_4254_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4248_ = lean_usize_dec_eq(v_i_4245_, v_stop_4246_);
                if v___x_4248_ == 0 {
                    v___x_4249_ = lean_array_uget_borrowed(v_as_4244_, v_i_4245_);
                    v_defValue_4250_ = crate::leanh::lean_ctor_get(v___x_4249_, 1);
                    v___x_4251_ = (crate::leanh::lean_unbox(v_defValue_4250_) as u8);
                    crate::leanh::lean_inc(v___x_4249_);
                    v___x_4252_ = l_Lean_Option_set___at___00Lean_Meta_withEqnOptions_spec__0(
                        v_b_4247_,
                        v___x_4249_,
                        v___x_4251_,
                    );
                    v___x_4253_ = 1usize;
                    v___x_4254_ = lean_usize_add(v_i_4245_, v___x_4253_);
                    v_i_4245_ = v___x_4254_;
                    v_b_4247_ = v___x_4252_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4247_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4___boxed(
    mut v_as_4256_: *mut crate::leanh::LeanObject,
    mut v_i_4257_: *mut crate::leanh::LeanObject,
    mut v_stop_4258_: *mut crate::leanh::LeanObject,
    mut v_b_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4260_: usize = 0;
    let mut v_stop_boxed_4261_: usize = 0;
    let mut v_res_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4260_ = crate::leanh::lean_unbox_usize(v_i_4257_);
    crate::leanh::lean_dec(v_i_4257_);
    v_stop_boxed_4261_ = crate::leanh::lean_unbox_usize(v_stop_4258_);
    crate::leanh::lean_dec(v_stop_4258_);
    v_res_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v_as_4256_, v_i_boxed_4260_, v_stop_boxed_4261_, v_b_4259_);
    crate::leanh::lean_dec_ref(v_as_4256_);
    return v_res_4262_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4263_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__0_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__0,
    );
    v___x_4265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4265_, 0, v___x_4264_);
    return v___x_4265_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__1_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__1,
    );
    v___x_4267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
    crate::leanh::lean_ctor_set(v___x_4267_, 1, v___x_4266_);
    return v___x_4267_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4268_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_4268_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = l_Lean_Meta_eqnAffectingOptions;
    v___x_4270_ = lean_array_get_size(v___x_4269_);
    return v___x_4270_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__5() -> u8 {
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    v___x_4271_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__4,
    );
    v___x_4272_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4273_ = lean_nat_dec_lt(v___x_4272_, v___x_4271_);
    return v___x_4273_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__6() -> u8 {
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    v___x_4274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__4,
    );
    v___x_4275_ = lean_nat_dec_le(v___x_4274_, v___x_4274_);
    return v___x_4275_;
}
pub unsafe fn _init_l_Lean_Meta_withEqnOptions___redArg___closed__7() -> usize {
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: usize = 0;
    v___x_4276_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__4_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__4,
    );
    v___x_4277_ = lean_usize_of_nat(v___x_4276_);
    return v___x_4277_;
}
pub unsafe fn l_Lean_Meta_withEqnOptions___redArg(
    mut v_declName_4278_: *mut crate::leanh::LeanObject,
    mut v_act_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4287_: u8 = 0;
    let mut v_fileName_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4299_: u8 = 0;
    let mut v_inheritedTraceOptions_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4324_: u8 = 0;
    let mut v_inheritedTraceOptions_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4328_: u8 = 0;
    let mut v___y_4329_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4341_: u8 = 0;
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut v_unused_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4362_: usize = 0;
    let mut v___x_4363_: usize = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: usize = 0;
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: usize = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: usize = 0;
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_st_ref_get(v_a_4283_);
                v___x_4307_ = lean_st_ref_get(v_a_4283_);
                v_env_4308_ = crate::leanh::lean_ctor_get(v___x_4306_, 0);
                crate::leanh::lean_inc_ref(v_env_4308_);
                crate::leanh::lean_dec(v___x_4306_);
                v___x_4309_ = l_Lean_Meta_eqnOptionsExt;
                v_toEnvExtension_4310_ = crate::leanh::lean_ctor_get(v___x_4309_, 0);
                v_asyncMode_4311_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4310_, 2);
                v_fileName_4312_ = crate::leanh::lean_ctor_get(v_a_4282_, 0);
                v_fileMap_4313_ = crate::leanh::lean_ctor_get(v_a_4282_, 1);
                v_options_4314_ = crate::leanh::lean_ctor_get(v_a_4282_, 2);
                v_currRecDepth_4315_ = crate::leanh::lean_ctor_get(v_a_4282_, 3);
                v_ref_4316_ = crate::leanh::lean_ctor_get(v_a_4282_, 5);
                v_currNamespace_4317_ = crate::leanh::lean_ctor_get(v_a_4282_, 6);
                v_openDecls_4318_ = crate::leanh::lean_ctor_get(v_a_4282_, 7);
                v_initHeartbeats_4319_ = crate::leanh::lean_ctor_get(v_a_4282_, 8);
                v_maxHeartbeats_4320_ = crate::leanh::lean_ctor_get(v_a_4282_, 9);
                v_quotContext_4321_ = crate::leanh::lean_ctor_get(v_a_4282_, 10);
                v_currMacroScope_4322_ = crate::leanh::lean_ctor_get(v_a_4282_, 11);
                v_cancelTk_x3f_4323_ = crate::leanh::lean_ctor_get(v_a_4282_, 12);
                v_suppressElabErrors_4324_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4282_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4325_ = crate::leanh::lean_ctor_get(v_a_4282_, 13);
                v___x_4356_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__3_once),
                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__3,
                );
                v___x_4357_ = 0;
                v___x_4358_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
                    v___x_4356_,
                    v___x_4309_,
                    v_env_4308_,
                    v_declName_4278_,
                    v_asyncMode_4311_,
                    v___x_4357_,
                );
                if crate::leanh::lean_obj_tag(v___x_4358_) == 1 {
                    v_val_4359_ = crate::leanh::lean_ctor_get(v___x_4358_, 0);
                    crate::leanh::lean_inc(v_val_4359_);
                    crate::leanh::lean_dec_ref_known(v___x_4358_, 1);
                    v___x_4365_ = l_Lean_Meta_eqnAffectingOptions;
                    v___x_4366_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_withEqnOptions___redArg___closed__5_once
                        ),
                        _init_l_Lean_Meta_withEqnOptions___redArg___closed__5,
                    );
                    if v___x_4366_ == 0 {
                        crate::leanh::lean_inc_ref(v_options_4314_);
                        v___y_4361_ = v_options_4314_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4367_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_withEqnOptions___redArg___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_withEqnOptions___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_withEqnOptions___redArg___closed__6,
                        );
                        if v___x_4367_ == 0 {
                            if v___x_4366_ == 0 {
                                crate::leanh::lean_inc_ref(v_options_4314_);
                                v___y_4361_ = v_options_4314_;
                                state = 6;
                                continue;
                            } else {
                                v___x_4368_ = 0usize;
                                v___x_4369_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_withEqnOptions___redArg___closed__7
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_withEqnOptions___redArg___closed__7_once
                                    ),
                                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__7,
                                );
                                crate::leanh::lean_inc_ref(v_options_4314_);
                                v___x_4370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_4365_, v___x_4368_, v___x_4369_, v_options_4314_);
                                v___y_4361_ = v___x_4370_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_4371_ = 0usize;
                            v___x_4372_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_withEqnOptions___redArg___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_withEqnOptions___redArg___closed__7_once
                                ),
                                _init_l_Lean_Meta_withEqnOptions___redArg___closed__7,
                            );
                            crate::leanh::lean_inc_ref(v_options_4314_);
                            v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_4365_, v___x_4371_, v___x_4372_, v_options_4314_);
                            v___y_4361_ = v___x_4373_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4358_);
                    v___x_4374_ = l_Lean_Meta_eqnAffectingOptions;
                    v___x_4375_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_withEqnOptions___redArg___closed__5_once
                        ),
                        _init_l_Lean_Meta_withEqnOptions___redArg___closed__5,
                    );
                    if v___x_4375_ == 0 {
                        crate::leanh::lean_inc_ref(v_options_4314_);
                        v___y_4351_ = v_options_4314_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4376_ = crate::leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_withEqnOptions___redArg___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_withEqnOptions___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_withEqnOptions___redArg___closed__6,
                        );
                        if v___x_4376_ == 0 {
                            if v___x_4375_ == 0 {
                                crate::leanh::lean_inc_ref(v_options_4314_);
                                v___y_4351_ = v_options_4314_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4377_ = 0usize;
                                v___x_4378_ = crate::leanh::lean_usize_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_withEqnOptions___redArg___closed__7
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_withEqnOptions___redArg___closed__7_once
                                    ),
                                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__7,
                                );
                                crate::leanh::lean_inc_ref(v_options_4314_);
                                v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_4374_, v___x_4377_, v___x_4378_, v_options_4314_);
                                v___y_4351_ = v___x_4379_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_4380_ = 0usize;
                            v___x_4381_ = crate::leanh::lean_usize_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_withEqnOptions___redArg___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_withEqnOptions___redArg___closed__7_once
                                ),
                                _init_l_Lean_Meta_withEqnOptions___redArg___closed__7,
                            );
                            crate::leanh::lean_inc_ref(v_options_4314_);
                            v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_withEqnOptions_spec__4(v___x_4374_, v___x_4380_, v___x_4381_, v_options_4314_);
                            v___y_4351_ = v___x_4382_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4302_ = l_Lean_maxRecDepth;
                v___x_4303_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(
                    v___y_4286_,
                    v___x_4302_,
                );
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4300_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4298_);
                crate::leanh::lean_inc(v_currMacroScope_4297_);
                crate::leanh::lean_inc(v_quotContext_4296_);
                crate::leanh::lean_inc(v_maxHeartbeats_4295_);
                crate::leanh::lean_inc(v_initHeartbeats_4294_);
                crate::leanh::lean_inc(v_openDecls_4293_);
                crate::leanh::lean_inc(v_currNamespace_4292_);
                crate::leanh::lean_inc(v_ref_4291_);
                crate::leanh::lean_inc(v_currRecDepth_4290_);
                crate::leanh::lean_inc_ref(v_fileMap_4289_);
                crate::leanh::lean_inc_ref(v_fileName_4288_);
                v___x_4304_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4304_, 0, v_fileName_4288_);
                crate::leanh::lean_ctor_set(v___x_4304_, 1, v_fileMap_4289_);
                crate::leanh::lean_ctor_set(v___x_4304_, 2, v___y_4286_);
                crate::leanh::lean_ctor_set(v___x_4304_, 3, v_currRecDepth_4290_);
                crate::leanh::lean_ctor_set(v___x_4304_, 4, v___x_4303_);
                crate::leanh::lean_ctor_set(v___x_4304_, 5, v_ref_4291_);
                crate::leanh::lean_ctor_set(v___x_4304_, 6, v_currNamespace_4292_);
                crate::leanh::lean_ctor_set(v___x_4304_, 7, v_openDecls_4293_);
                crate::leanh::lean_ctor_set(v___x_4304_, 8, v_initHeartbeats_4294_);
                crate::leanh::lean_ctor_set(v___x_4304_, 9, v_maxHeartbeats_4295_);
                crate::leanh::lean_ctor_set(v___x_4304_, 10, v_quotContext_4296_);
                crate::leanh::lean_ctor_set(v___x_4304_, 11, v_currMacroScope_4297_);
                crate::leanh::lean_ctor_set(v___x_4304_, 12, v_cancelTk_x3f_4298_);
                crate::leanh::lean_ctor_set(v___x_4304_, 13, v_inheritedTraceOptions_4300_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4304_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v___y_4287_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4304_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4299_,
                );
                crate::leanh::lean_inc(v___y_4301_);
                crate::leanh::lean_inc(v_a_4281_);
                crate::leanh::lean_inc_ref(v_a_4280_);
                v___x_4305_ = crate::leanh::lean_apply_5(
                    v_act_4279_,
                    v_a_4280_,
                    v_a_4281_,
                    v___x_4304_,
                    v___y_4301_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4305_;
            }
            2 => {
                if v___y_4329_ == 0 {
                    v___x_4330_ = lean_st_ref_take(v_a_4283_);
                    v_env_4331_ = crate::leanh::lean_ctor_get(v___x_4330_, 0);
                    v_nextMacroScope_4332_ = crate::leanh::lean_ctor_get(v___x_4330_, 1);
                    v_ngen_4333_ = crate::leanh::lean_ctor_get(v___x_4330_, 2);
                    v_auxDeclNGen_4334_ = crate::leanh::lean_ctor_get(v___x_4330_, 3);
                    v_traceState_4335_ = crate::leanh::lean_ctor_get(v___x_4330_, 4);
                    v_messages_4336_ = crate::leanh::lean_ctor_get(v___x_4330_, 6);
                    v_infoState_4337_ = crate::leanh::lean_ctor_get(v___x_4330_, 7);
                    v_snapshotTasks_4338_ = crate::leanh::lean_ctor_get(v___x_4330_, 8);
                    v_isSharedCheck_4348_ = (!crate::leanh::lean_is_exclusive(v___x_4330_)) as u8;
                    if v_isSharedCheck_4348_ == 0 {
                        v_unused_4349_ = crate::leanh::lean_ctor_get(v___x_4330_, 5);
                        crate::leanh::lean_dec(v_unused_4349_);
                        v___x_4340_ = v___x_4330_;
                        v_isShared_4341_ = v_isSharedCheck_4348_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_4338_);
                        crate::leanh::lean_inc(v_infoState_4337_);
                        crate::leanh::lean_inc(v_messages_4336_);
                        crate::leanh::lean_inc(v_traceState_4335_);
                        crate::leanh::lean_inc(v_auxDeclNGen_4334_);
                        crate::leanh::lean_inc(v_ngen_4333_);
                        crate::leanh::lean_inc(v_nextMacroScope_4332_);
                        crate::leanh::lean_inc(v_env_4331_);
                        crate::leanh::lean_dec(v___x_4330_);
                        v___x_4340_ = crate::leanh::lean_box(0);
                        v_isShared_4341_ = v_isSharedCheck_4348_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_4286_ = v___y_4327_;
                    v___y_4287_ = v___y_4328_;
                    v_fileName_4288_ = v_fileName_4312_;
                    v_fileMap_4289_ = v_fileMap_4313_;
                    v_currRecDepth_4290_ = v_currRecDepth_4315_;
                    v_ref_4291_ = v_ref_4316_;
                    v_currNamespace_4292_ = v_currNamespace_4317_;
                    v_openDecls_4293_ = v_openDecls_4318_;
                    v_initHeartbeats_4294_ = v_initHeartbeats_4319_;
                    v_maxHeartbeats_4295_ = v_maxHeartbeats_4320_;
                    v_quotContext_4296_ = v_quotContext_4321_;
                    v_currMacroScope_4297_ = v_currMacroScope_4322_;
                    v_cancelTk_x3f_4298_ = v_cancelTk_x3f_4323_;
                    v_suppressElabErrors_4299_ = v_suppressElabErrors_4324_;
                    v_inheritedTraceOptions_4300_ = v_inheritedTraceOptions_4325_;
                    v___y_4301_ = v_a_4283_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4342_ = l_Lean_Kernel_enableDiag(v_env_4331_, v___y_4328_);
                v___x_4343_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2_once),
                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__2,
                );
                if v_isShared_4341_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4340_, 5, v___x_4343_);
                    crate::leanh::lean_ctor_set(v___x_4340_, 0, v___x_4342_);
                    v___x_4345_ = v___x_4340_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4347_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_nextMacroScope_4332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 2, v_ngen_4333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 3, v_auxDeclNGen_4334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 4, v_traceState_4335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 5, v___x_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 6, v_messages_4336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 7, v_infoState_4337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 8, v_snapshotTasks_4338_);
                    v___x_4345_ = v_reuseFailAlloc_4347_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4346_ = lean_st_ref_set(v_a_4283_, v___x_4345_);
                v___y_4286_ = v___y_4327_;
                v___y_4287_ = v___y_4328_;
                v_fileName_4288_ = v_fileName_4312_;
                v_fileMap_4289_ = v_fileMap_4313_;
                v_currRecDepth_4290_ = v_currRecDepth_4315_;
                v_ref_4291_ = v_ref_4316_;
                v_currNamespace_4292_ = v_currNamespace_4317_;
                v_openDecls_4293_ = v_openDecls_4318_;
                v_initHeartbeats_4294_ = v_initHeartbeats_4319_;
                v_maxHeartbeats_4295_ = v_maxHeartbeats_4320_;
                v_quotContext_4296_ = v_quotContext_4321_;
                v_currMacroScope_4297_ = v_currMacroScope_4322_;
                v_cancelTk_x3f_4298_ = v_cancelTk_x3f_4323_;
                v_suppressElabErrors_4299_ = v_suppressElabErrors_4324_;
                v_inheritedTraceOptions_4300_ = v_inheritedTraceOptions_4325_;
                v___y_4301_ = v_a_4283_;
                state = 1;
                continue;
            }
            5 => {
                v_env_4352_ = crate::leanh::lean_ctor_get(v___x_4307_, 0);
                crate::leanh::lean_inc_ref(v_env_4352_);
                crate::leanh::lean_dec(v___x_4307_);
                v___x_4353_ = l_Lean_diagnostics;
                v___x_4354_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                    v___y_4351_,
                    v___x_4353_,
                );
                v___x_4355_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4352_);
                crate::leanh::lean_dec_ref(v_env_4352_);
                if v___x_4355_ == 0 {
                    if v___x_4354_ == 0 {
                        v___y_4286_ = v___y_4351_;
                        v___y_4287_ = v___x_4354_;
                        v_fileName_4288_ = v_fileName_4312_;
                        v_fileMap_4289_ = v_fileMap_4313_;
                        v_currRecDepth_4290_ = v_currRecDepth_4315_;
                        v_ref_4291_ = v_ref_4316_;
                        v_currNamespace_4292_ = v_currNamespace_4317_;
                        v_openDecls_4293_ = v_openDecls_4318_;
                        v_initHeartbeats_4294_ = v_initHeartbeats_4319_;
                        v_maxHeartbeats_4295_ = v_maxHeartbeats_4320_;
                        v_quotContext_4296_ = v_quotContext_4321_;
                        v_currMacroScope_4297_ = v_currMacroScope_4322_;
                        v_cancelTk_x3f_4298_ = v_cancelTk_x3f_4323_;
                        v_suppressElabErrors_4299_ = v_suppressElabErrors_4324_;
                        v_inheritedTraceOptions_4300_ = v_inheritedTraceOptions_4325_;
                        v___y_4301_ = v_a_4283_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4327_ = v___y_4351_;
                        v___y_4328_ = v___x_4354_;
                        v___y_4329_ = v___x_4355_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_4327_ = v___y_4351_;
                    v___y_4328_ = v___x_4354_;
                    v___y_4329_ = v___x_4354_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v_sz_4362_ = lean_array_size(v_val_4359_);
                v___x_4363_ = 0usize;
                v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3(v_val_4359_, v_sz_4362_, v___x_4363_, v___y_4361_);
                crate::leanh::lean_dec(v_val_4359_);
                v___y_4351_ = v___x_4364_;
                state = 5;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withEqnOptions___redArg___boxed(
    mut v_declName_4383_: *mut crate::leanh::LeanObject,
    mut v_act_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lean_Meta_withEqnOptions___redArg(
        v_declName_4383_,
        v_act_4384_,
        v_a_4385_,
        v_a_4386_,
        v_a_4387_,
        v_a_4388_,
    );
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    crate::leanh::lean_dec(v_a_4386_);
    crate::leanh::lean_dec_ref(v_a_4385_);
    return v_res_4390_;
}
pub unsafe fn l_Lean_Meta_withEqnOptions(
    mut v_00_u03b1_4391_: *mut crate::leanh::LeanObject,
    mut v_declName_4392_: *mut crate::leanh::LeanObject,
    mut v_act_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_Meta_withEqnOptions___redArg(
        v_declName_4392_,
        v_act_4393_,
        v_a_4394_,
        v_a_4395_,
        v_a_4396_,
        v_a_4397_,
    );
    return v___x_4399_;
}
pub unsafe fn l_Lean_Meta_withEqnOptions___boxed(
    mut v_00_u03b1_4400_: *mut crate::leanh::LeanObject,
    mut v_declName_4401_: *mut crate::leanh::LeanObject,
    mut v_act_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
    mut v_a_4406_: *mut crate::leanh::LeanObject,
    mut v_a_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Lean_Meta_withEqnOptions(
        v_00_u03b1_4400_,
        v_declName_4401_,
        v_act_4402_,
        v_a_4403_,
        v_a_4404_,
        v_a_4405_,
        v_a_4406_,
    );
    crate::leanh::lean_dec(v_a_4406_);
    crate::leanh::lean_dec_ref(v_a_4405_);
    crate::leanh::lean_dec(v_a_4404_);
    crate::leanh::lean_dec_ref(v_a_4403_);
    return v_res_4408_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(
    mut v_thm_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: u8 = 0;
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: u8 = 0;
    let mut v___x_4428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4412_ = lean_st_ref_get(v___y_4410_);
                v_env_4413_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4413_, 2);
                crate::leanh::lean_dec(v___x_4412_);
                v_toConstantVal_4414_ = crate::leanh::lean_ctor_get(v_thm_4409_, 0);
                v_value_4415_ = crate::leanh::lean_ctor_get(v_thm_4409_, 1);
                v_all_4416_ = crate::leanh::lean_ctor_get(v_thm_4409_, 2);
                v_type_4426_ = crate::leanh::lean_ctor_get(v_toConstantVal_4414_, 2);
                v___x_4427_ = l_Lean_Environment_hasUnsafe(v_env_4413_, v_type_4426_);
                if v___x_4427_ == 0 {
                    v___x_4428_ = l_Lean_Environment_hasUnsafe(v_env_4413_, v_value_4415_);
                    v___y_4418_ = v___x_4428_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_4413_);
                    v___y_4418_ = v___x_4427_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4418_ == 0 {
                    v___x_4419_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4419_, 0, v_thm_4409_);
                    v___x_4420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4420_, 0, v___x_4419_);
                    return v___x_4420_;
                } else {
                    crate::leanh::lean_inc(v_all_4416_);
                    crate::leanh::lean_inc_ref(v_value_4415_);
                    crate::leanh::lean_inc_ref(v_toConstantVal_4414_);
                    crate::leanh::lean_dec_ref(v_thm_4409_);
                    v___x_4421_ = crate::leanh::lean_box(0);
                    v___x_4422_ = 0;
                    v___x_4423_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4423_, 0, v_toConstantVal_4414_);
                    crate::leanh::lean_ctor_set(v___x_4423_, 1, v_value_4415_);
                    crate::leanh::lean_ctor_set(v___x_4423_, 2, v___x_4421_);
                    crate::leanh::lean_ctor_set(v___x_4423_, 3, v_all_4416_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4423_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                        v___x_4422_,
                    );
                    v___x_4424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4424_, 0, v___x_4423_);
                    v___x_4425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4424_);
                    return v___x_4425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg___boxed(
    mut v_thm_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_4429_, v___y_4430_);
    crate::leanh::lean_dec(v___y_4430_);
    return v_res_4432_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(
    mut v_thm_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
    mut v___y_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v_thm_4433_, v___y_4437_);
    return v___x_4439_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___boxed(
    mut v_thm_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1(v_thm_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
    crate::leanh::lean_dec(v___y_4444_);
    crate::leanh::lean_dec_ref(v___y_4443_);
    crate::leanh::lean_dec(v___y_4442_);
    crate::leanh::lean_dec_ref(v___y_4441_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(
    mut v_k_4447_: *mut crate::leanh::LeanObject,
    mut v_b_4448_: *mut crate::leanh::LeanObject,
    mut v_c_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4453_);
    crate::leanh::lean_inc_ref(v___y_4452_);
    crate::leanh::lean_inc(v___y_4451_);
    crate::leanh::lean_inc_ref(v___y_4450_);
    v___x_4455_ = crate::leanh::lean_apply_7(
        v_k_4447_,
        v_b_4448_,
        v_c_4449_,
        v___y_4450_,
        v___y_4451_,
        v___y_4452_,
        v___y_4453_,
        crate::leanh::lean_box(0),
    );
    return v___x_4455_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed(
    mut v_k_4456_: *mut crate::leanh::LeanObject,
    mut v_b_4457_: *mut crate::leanh::LeanObject,
    mut v_c_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
    mut v___y_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4464_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0(v_k_4456_, v_b_4457_, v_c_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
    crate::leanh::lean_dec(v___y_4462_);
    crate::leanh::lean_dec_ref(v___y_4461_);
    crate::leanh::lean_dec(v___y_4460_);
    crate::leanh::lean_dec_ref(v___y_4459_);
    return v_res_4464_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(
    mut v_e_4465_: *mut crate::leanh::LeanObject,
    mut v_k_4466_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4467_: u8,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: u8 = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4473_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4473_, 0, v_k_4466_);
                v___x_4474_ = 1;
                v___x_4475_ = 0;
                v___x_4476_ = crate::leanh::lean_box(0);
                v___x_4477_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_4465_,
                    v___x_4474_,
                    v___x_4475_,
                    v___x_4474_,
                    v___x_4475_,
                    v___x_4476_,
                    v___f_4473_,
                    v_cleanupAnnotations_4467_,
                    v___y_4468_,
                    v___y_4469_,
                    v___y_4470_,
                    v___y_4471_,
                );
                if crate::leanh::lean_obj_tag(v___x_4477_) == 0 {
                    v_a_4478_ = crate::leanh::lean_ctor_get(v___x_4477_, 0);
                    v_isSharedCheck_4485_ = (!crate::leanh::lean_is_exclusive(v___x_4477_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4480_ = v___x_4477_;
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4478_);
                        crate::leanh::lean_dec(v___x_4477_);
                        v___x_4480_ = crate::leanh::lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4477_, 0);
                    v_isSharedCheck_4493_ = (!crate::leanh::lean_is_exclusive(v___x_4477_)) as u8;
                    if v_isSharedCheck_4493_ == 0 {
                        v___x_4488_ = v___x_4477_;
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4486_);
                        crate::leanh::lean_dec(v___x_4477_);
                        v___x_4488_ = crate::leanh::lean_box(0);
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4481_ == 0 {
                    v___x_4483_ = v___x_4480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4483_;
            }
            3 => {
                if v_isShared_4489_ == 0 {
                    v___x_4491_ = v___x_4488_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg___boxed(
    mut v_e_4494_: *mut crate::leanh::LeanObject,
    mut v_k_4495_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4496_: *mut crate::leanh::LeanObject,
    mut v___y_4497_: *mut crate::leanh::LeanObject,
    mut v___y_4498_: *mut crate::leanh::LeanObject,
    mut v___y_4499_: *mut crate::leanh::LeanObject,
    mut v___y_4500_: *mut crate::leanh::LeanObject,
    mut v___y_4501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4502_: u8 = 0;
    let mut v_res_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4502_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4496_) as u8);
    v_res_4503_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_4494_, v_k_4495_, v_cleanupAnnotations_boxed_4502_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
    crate::leanh::lean_dec(v___y_4500_);
    crate::leanh::lean_dec_ref(v___y_4499_);
    crate::leanh::lean_dec(v___y_4498_);
    crate::leanh::lean_dec_ref(v___y_4497_);
    return v_res_4503_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(
    mut v_00_u03b1_4504_: *mut crate::leanh::LeanObject,
    mut v_e_4505_: *mut crate::leanh::LeanObject,
    mut v_k_4506_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4507_: u8,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4513_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_e_4505_, v_k_4506_, v_cleanupAnnotations_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
    return v___x_4513_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___boxed(
    mut v_00_u03b1_4514_: *mut crate::leanh::LeanObject,
    mut v_e_4515_: *mut crate::leanh::LeanObject,
    mut v_k_4516_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4523_: u8 = 0;
    let mut v_res_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4523_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4517_) as u8);
    v_res_4524_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2(v_00_u03b1_4514_, v_e_4515_, v_k_4516_, v_cleanupAnnotations_boxed_4523_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
    crate::leanh::lean_dec(v___y_4521_);
    crate::leanh::lean_dec_ref(v___y_4520_);
    crate::leanh::lean_dec(v___y_4519_);
    crate::leanh::lean_dec_ref(v___y_4518_);
    return v_res_4524_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4532_: u8 = 0;
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4525_) == 0 {
                    v___x_4527_ = l_List_reverse___redArg(v_a_4526_);
                    return v___x_4527_;
                } else {
                    v_head_4528_ = crate::leanh::lean_ctor_get(v_a_4525_, 0);
                    v_tail_4529_ = crate::leanh::lean_ctor_get(v_a_4525_, 1);
                    v_isSharedCheck_4538_ = (!crate::leanh::lean_is_exclusive(v_a_4525_)) as u8;
                    if v_isSharedCheck_4538_ == 0 {
                        v___x_4531_ = v_a_4525_;
                        v_isShared_4532_ = v_isSharedCheck_4538_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4529_);
                        crate::leanh::lean_inc(v_head_4528_);
                        crate::leanh::lean_dec(v_a_4525_);
                        v___x_4531_ = crate::leanh::lean_box(0);
                        v_isShared_4532_ = v_isSharedCheck_4538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4533_ = l_Lean_mkLevelParam(v_head_4528_);
                if v_isShared_4532_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4531_, 1, v_a_4526_);
                    crate::leanh::lean_ctor_set(v___x_4531_, 0, v___x_4533_);
                    v___x_4535_ = v___x_4531_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_a_4526_);
                    v___x_4535_ = v_reuseFailAlloc_4537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4525_ = v_tail_4529_;
                v_a_4526_ = v___x_4535_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(
    mut v_toConstantVal_4539_: *mut crate::leanh::LeanObject,
    mut v_name_4540_: *mut crate::leanh::LeanObject,
    mut v_xs_4541_: *mut crate::leanh::LeanObject,
    mut v_body_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: u8 = 0;
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4586_: u8 = 0;
    let mut v_a_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4590_: u8 = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4594_: u8 = 0;
    let mut v_a_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4598_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_a_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v_a_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_isSharedCheck_4619_: u8 = 0;
    let mut v_unused_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_4548_ = crate::leanh::lean_ctor_get(v_toConstantVal_4539_, 0);
                v_levelParams_4549_ = crate::leanh::lean_ctor_get(v_toConstantVal_4539_, 1);
                v_isSharedCheck_4619_ =
                    (!crate::leanh::lean_is_exclusive(v_toConstantVal_4539_)) as u8;
                if v_isSharedCheck_4619_ == 0 {
                    v_unused_4620_ = crate::leanh::lean_ctor_get(v_toConstantVal_4539_, 2);
                    crate::leanh::lean_dec(v_unused_4620_);
                    v___x_4551_ = v_toConstantVal_4539_;
                    v_isShared_4552_ = v_isSharedCheck_4619_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_levelParams_4549_);
                    crate::leanh::lean_inc(v_name_4548_);
                    crate::leanh::lean_dec(v_toConstantVal_4539_);
                    v___x_4551_ = crate::leanh::lean_box(0);
                    v_isShared_4552_ = v_isSharedCheck_4619_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4553_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_levelParams_4549_);
                v___x_4554_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__0(v_levelParams_4549_, v___x_4553_);
                v___x_4555_ = l_Lean_mkConst(v_name_4548_, v___x_4554_);
                v_lhs_4556_ = l_Lean_mkAppN(v___x_4555_, v_xs_4541_);
                crate::leanh::lean_inc_ref(v_lhs_4556_);
                v___x_4557_ = l_Lean_Meta_mkEq(
                    v_lhs_4556_,
                    v_body_4542_,
                    v___y_4543_,
                    v___y_4544_,
                    v___y_4545_,
                    v___y_4546_,
                );
                if crate::leanh::lean_obj_tag(v___x_4557_) == 0 {
                    v_a_4558_ = crate::leanh::lean_ctor_get(v___x_4557_, 0);
                    crate::leanh::lean_inc(v_a_4558_);
                    crate::leanh::lean_dec_ref_known(v___x_4557_, 1);
                    v___x_4559_ = 0;
                    v___x_4560_ = 1;
                    v___x_4561_ = 1;
                    v___x_4562_ = l_Lean_Meta_mkForallFVars(
                        v_xs_4541_,
                        v_a_4558_,
                        v___x_4559_,
                        v___x_4560_,
                        v___x_4560_,
                        v___x_4561_,
                        v___y_4543_,
                        v___y_4544_,
                        v___y_4545_,
                        v___y_4546_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4562_) == 0 {
                        v_a_4563_ = crate::leanh::lean_ctor_get(v___x_4562_, 0);
                        crate::leanh::lean_inc(v_a_4563_);
                        crate::leanh::lean_dec_ref_known(v___x_4562_, 1);
                        v___x_4564_ = l_Lean_Meta_letToHave(
                            v_a_4563_,
                            v___y_4543_,
                            v___y_4544_,
                            v___y_4545_,
                            v___y_4546_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4564_) == 0 {
                            v_a_4565_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                            crate::leanh::lean_inc(v_a_4565_);
                            crate::leanh::lean_dec_ref_known(v___x_4564_, 1);
                            v___x_4566_ = l_Lean_Meta_mkEqRefl(
                                v_lhs_4556_,
                                v___y_4543_,
                                v___y_4544_,
                                v___y_4545_,
                                v___y_4546_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4566_) == 0 {
                                v_a_4567_ = crate::leanh::lean_ctor_get(v___x_4566_, 0);
                                crate::leanh::lean_inc(v_a_4567_);
                                crate::leanh::lean_dec_ref_known(v___x_4566_, 1);
                                v___x_4568_ = l_Lean_Meta_mkLambdaFVars(
                                    v_xs_4541_,
                                    v_a_4567_,
                                    v___x_4559_,
                                    v___x_4560_,
                                    v___x_4559_,
                                    v___x_4560_,
                                    v___x_4561_,
                                    v___y_4543_,
                                    v___y_4544_,
                                    v___y_4545_,
                                    v___y_4546_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4568_) == 0 {
                                    v_a_4569_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                                    crate::leanh::lean_inc(v_a_4569_);
                                    crate::leanh::lean_dec_ref_known(v___x_4568_, 1);
                                    crate::leanh::lean_inc(v_name_4540_);
                                    if v_isShared_4552_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4551_, 2, v_a_4565_);
                                        crate::leanh::lean_ctor_set(v___x_4551_, 0, v_name_4540_);
                                        v___x_4571_ = v___x_4551_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4578_ =
                                            crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4578_,
                                            0,
                                            v_name_4540_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4578_,
                                            1,
                                            v_levelParams_4549_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4578_,
                                            2,
                                            v_a_4565_,
                                        );
                                        v___x_4571_ = v_reuseFailAlloc_4578_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4565_);
                                    crate::leanh::lean_del_object(v___x_4551_);
                                    crate::leanh::lean_dec(v_levelParams_4549_);
                                    crate::leanh::lean_dec(v_name_4540_);
                                    v_a_4579_ = crate::leanh::lean_ctor_get(v___x_4568_, 0);
                                    v_isSharedCheck_4586_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4568_)) as u8;
                                    if v_isSharedCheck_4586_ == 0 {
                                        v___x_4581_ = v___x_4568_;
                                        v_isShared_4582_ = v_isSharedCheck_4586_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4579_);
                                        crate::leanh::lean_dec(v___x_4568_);
                                        v___x_4581_ = crate::leanh::lean_box(0);
                                        v_isShared_4582_ = v_isSharedCheck_4586_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4565_);
                                crate::leanh::lean_del_object(v___x_4551_);
                                crate::leanh::lean_dec(v_levelParams_4549_);
                                crate::leanh::lean_dec(v_name_4540_);
                                v_a_4587_ = crate::leanh::lean_ctor_get(v___x_4566_, 0);
                                v_isSharedCheck_4594_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4566_)) as u8;
                                if v_isSharedCheck_4594_ == 0 {
                                    v___x_4589_ = v___x_4566_;
                                    v_isShared_4590_ = v_isSharedCheck_4594_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4587_);
                                    crate::leanh::lean_dec(v___x_4566_);
                                    v___x_4589_ = crate::leanh::lean_box(0);
                                    v_isShared_4590_ = v_isSharedCheck_4594_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_lhs_4556_);
                            crate::leanh::lean_del_object(v___x_4551_);
                            crate::leanh::lean_dec(v_levelParams_4549_);
                            crate::leanh::lean_dec(v_name_4540_);
                            v_a_4595_ = crate::leanh::lean_ctor_get(v___x_4564_, 0);
                            v_isSharedCheck_4602_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4564_)) as u8;
                            if v_isSharedCheck_4602_ == 0 {
                                v___x_4597_ = v___x_4564_;
                                v_isShared_4598_ = v_isSharedCheck_4602_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4595_);
                                crate::leanh::lean_dec(v___x_4564_);
                                v___x_4597_ = crate::leanh::lean_box(0);
                                v_isShared_4598_ = v_isSharedCheck_4602_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_lhs_4556_);
                        crate::leanh::lean_del_object(v___x_4551_);
                        crate::leanh::lean_dec(v_levelParams_4549_);
                        crate::leanh::lean_dec(v_name_4540_);
                        v_a_4603_ = crate::leanh::lean_ctor_get(v___x_4562_, 0);
                        v_isSharedCheck_4610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4562_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4605_ = v___x_4562_;
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4603_);
                            crate::leanh::lean_dec(v___x_4562_);
                            v___x_4605_ = crate::leanh::lean_box(0);
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_lhs_4556_);
                    crate::leanh::lean_del_object(v___x_4551_);
                    crate::leanh::lean_dec(v_levelParams_4549_);
                    crate::leanh::lean_dec(v_name_4540_);
                    v_a_4611_ = crate::leanh::lean_ctor_get(v___x_4557_, 0);
                    v_isSharedCheck_4618_ = (!crate::leanh::lean_is_exclusive(v___x_4557_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___x_4557_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4611_);
                        crate::leanh::lean_dec(v___x_4557_);
                        v___x_4613_ = crate::leanh::lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc(v_name_4540_);
                v___x_4572_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4572_, 0, v_name_4540_);
                crate::leanh::lean_ctor_set(v___x_4572_, 1, v___x_4553_);
                v___x_4573_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4573_, 0, v___x_4571_);
                crate::leanh::lean_ctor_set(v___x_4573_, 1, v_a_4569_);
                crate::leanh::lean_ctor_set(v___x_4573_, 2, v___x_4572_);
                v___x_4574_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__1___redArg(v___x_4573_, v___y_4546_);
                v_a_4575_ = crate::leanh::lean_ctor_get(v___x_4574_, 0);
                crate::leanh::lean_inc(v_a_4575_);
                crate::leanh::lean_dec_ref(v___x_4574_);
                v___x_4576_ = l_Lean_addDecl(v_a_4575_, v___x_4559_, v___y_4545_, v___y_4546_);
                if crate::leanh::lean_obj_tag(v___x_4576_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4576_, 1);
                    v___x_4577_ = l_Lean_inferDefEqAttr(
                        v_name_4540_,
                        v___y_4543_,
                        v___y_4544_,
                        v___y_4545_,
                        v___y_4546_,
                    );
                    return v___x_4577_;
                } else {
                    crate::leanh::lean_dec(v_name_4540_);
                    return v___x_4576_;
                }
            }
            3 => {
                if v_isShared_4582_ == 0 {
                    v___x_4584_ = v___x_4581_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
                    v___x_4584_ = v_reuseFailAlloc_4585_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4584_;
            }
            5 => {
                if v_isShared_4590_ == 0 {
                    v___x_4592_ = v___x_4589_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
                    v___x_4592_ = v_reuseFailAlloc_4593_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4592_;
            }
            7 => {
                if v_isShared_4598_ == 0 {
                    v___x_4600_ = v___x_4597_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
                    v___x_4600_ = v_reuseFailAlloc_4601_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4600_;
            }
            9 => {
                if v_isShared_4606_ == 0 {
                    v___x_4608_ = v___x_4605_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4608_;
            }
            11 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(
    mut v_toConstantVal_4621_: *mut crate::leanh::LeanObject,
    mut v_name_4622_: *mut crate::leanh::LeanObject,
    mut v_xs_4623_: *mut crate::leanh::LeanObject,
    mut v_body_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(
        v_toConstantVal_4621_,
        v_name_4622_,
        v_xs_4623_,
        v_body_4624_,
        v___y_4625_,
        v___y_4626_,
        v___y_4627_,
        v___y_4628_,
    );
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec_ref(v_xs_4623_);
    return v_res_4630_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(
    mut v_name_4631_: *mut crate::leanh::LeanObject,
    mut v_info_4632_: *mut crate::leanh::LeanObject,
    mut v_a_4633_: *mut crate::leanh::LeanObject,
    mut v_a_4634_: *mut crate::leanh::LeanObject,
    mut v_a_4635_: *mut crate::leanh::LeanObject,
    mut v_a_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toConstantVal_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: u8 = 0;
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toConstantVal_4638_ = crate::leanh::lean_ctor_get(v_info_4632_, 0);
    crate::leanh::lean_inc_ref(v_toConstantVal_4638_);
    v_value_4639_ = crate::leanh::lean_ctor_get(v_info_4632_, 1);
    crate::leanh::lean_inc_ref(v_value_4639_);
    crate::leanh::lean_dec_ref(v_info_4632_);
    v___f_4640_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4640_, 0, v_toConstantVal_4638_);
    crate::leanh::lean_closure_set(v___f_4640_, 1, v_name_4631_);
    v___x_4641_ = 1;
    v___x_4642_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize_spec__2___redArg(v_value_4639_, v___f_4640_, v___x_4641_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
    return v___x_4642_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed(
    mut v_name_4643_: *mut crate::leanh::LeanObject,
    mut v_info_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v_a_4646_: *mut crate::leanh::LeanObject,
    mut v_a_4647_: *mut crate::leanh::LeanObject,
    mut v_a_4648_: *mut crate::leanh::LeanObject,
    mut v_a_4649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4650_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(
        v_name_4643_,
        v_info_4644_,
        v_a_4645_,
        v_a_4646_,
        v_a_4647_,
        v_a_4648_,
    );
    crate::leanh::lean_dec(v_a_4648_);
    crate::leanh::lean_dec_ref(v_a_4647_);
    crate::leanh::lean_dec(v_a_4646_);
    crate::leanh::lean_dec_ref(v_a_4645_);
    return v_res_4650_;
}
pub unsafe fn l_Lean_Meta_mkSimpleEqThm(
    mut v_declName_4651_: *mut crate::leanh::LeanObject,
    mut v_name_4652_: *mut crate::leanh::LeanObject,
    mut v_a_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_a_4656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: u8 = 0;
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4668_: u8 = 0;
    let mut v_val_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4682_: u8 = 0;
    let mut v_unused_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4687_: u8 = 0;
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4661_ = lean_st_ref_get(v_a_4656_);
                v_env_4662_ = crate::leanh::lean_ctor_get(v___x_4661_, 0);
                crate::leanh::lean_inc_ref(v_env_4662_);
                crate::leanh::lean_dec(v___x_4661_);
                v___x_4663_ = 0;
                crate::leanh::lean_inc(v_declName_4651_);
                v___x_4664_ =
                    l_Lean_Environment_find_x3f(v_env_4662_, v_declName_4651_, v___x_4663_);
                if crate::leanh::lean_obj_tag(v___x_4664_) == 1 {
                    v_val_4665_ = crate::leanh::lean_ctor_get(v___x_4664_, 0);
                    v_isSharedCheck_4692_ = (!crate::leanh::lean_is_exclusive(v___x_4664_)) as u8;
                    if v_isSharedCheck_4692_ == 0 {
                        v___x_4667_ = v___x_4664_;
                        v_isShared_4668_ = v_isSharedCheck_4692_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4665_);
                        crate::leanh::lean_dec(v___x_4664_);
                        v___x_4667_ = crate::leanh::lean_box(0);
                        v_isShared_4668_ = v_isSharedCheck_4692_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4664_);
                    crate::leanh::lean_dec(v_name_4652_);
                    crate::leanh::lean_dec(v_declName_4651_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4659_ = crate::leanh::lean_box(0);
                v___x_4660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4660_, 0, v___x_4659_);
                return v___x_4660_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_4665_) == 1 {
                    v_val_4669_ = crate::leanh::lean_ctor_get(v_val_4665_, 0);
                    crate::leanh::lean_inc_ref(v_val_4669_);
                    crate::leanh::lean_dec_ref_known(v_val_4665_, 1);
                    crate::leanh::lean_inc_n(v_name_4652_, 2);
                    v___x_4670_ = crate::leanh::lean_alloc_closure(
                        l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_4670_, 0, v_name_4652_);
                    crate::leanh::lean_closure_set(v___x_4670_, 1, v_val_4669_);
                    crate::leanh::lean_inc(v_declName_4651_);
                    v___x_4671_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_withEqnOptions___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_4671_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_4671_, 1, v_declName_4651_);
                    crate::leanh::lean_closure_set(v___x_4671_, 2, v___x_4670_);
                    v___x_4672_ = l_Lean_Meta_realizeConst(
                        v_declName_4651_,
                        v_name_4652_,
                        v___x_4671_,
                        v_a_4653_,
                        v_a_4654_,
                        v_a_4655_,
                        v_a_4656_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4672_) == 0 {
                        v_isSharedCheck_4682_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4672_)) as u8;
                        if v_isSharedCheck_4682_ == 0 {
                            v_unused_4683_ = crate::leanh::lean_ctor_get(v___x_4672_, 0);
                            crate::leanh::lean_dec(v_unused_4683_);
                            v___x_4674_ = v___x_4672_;
                            v_isShared_4675_ = v_isSharedCheck_4682_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4672_);
                            v___x_4674_ = crate::leanh::lean_box(0);
                            v_isShared_4675_ = v_isSharedCheck_4682_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4667_);
                        crate::leanh::lean_dec(v_name_4652_);
                        v_a_4684_ = crate::leanh::lean_ctor_get(v___x_4672_, 0);
                        v_isSharedCheck_4691_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4672_)) as u8;
                        if v_isSharedCheck_4691_ == 0 {
                            v___x_4686_ = v___x_4672_;
                            v_isShared_4687_ = v_isSharedCheck_4691_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4684_);
                            crate::leanh::lean_dec(v___x_4672_);
                            v___x_4686_ = crate::leanh::lean_box(0);
                            v_isShared_4687_ = v_isSharedCheck_4691_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4667_);
                    crate::leanh::lean_dec(v_val_4665_);
                    crate::leanh::lean_dec(v_name_4652_);
                    crate::leanh::lean_dec(v_declName_4651_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4668_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4667_, 0, v_name_4652_);
                    v___x_4677_ = v___x_4667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4681_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_name_4652_);
                    v___x_4677_ = v_reuseFailAlloc_4681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4674_, 0, v___x_4677_);
                    v___x_4679_ = v___x_4674_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
                    v___x_4679_ = v_reuseFailAlloc_4680_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4679_;
            }
            6 => {
                if v_isShared_4687_ == 0 {
                    v___x_4689_ = v___x_4686_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_a_4684_);
                    v___x_4689_ = v_reuseFailAlloc_4690_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSimpleEqThm___boxed(
    mut v_declName_4693_: *mut crate::leanh::LeanObject,
    mut v_name_4694_: *mut crate::leanh::LeanObject,
    mut v_a_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_a_4697_: *mut crate::leanh::LeanObject,
    mut v_a_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4700_ = l_Lean_Meta_mkSimpleEqThm(
        v_declName_4693_,
        v_name_4694_,
        v_a_4695_,
        v_a_4696_,
        v_a_4697_,
        v_a_4698_,
    );
    crate::leanh::lean_dec(v_a_4698_);
    crate::leanh::lean_dec_ref(v_a_4697_);
    crate::leanh::lean_dec(v_a_4696_);
    crate::leanh::lean_dec_ref(v_a_4695_);
    return v_res_4700_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4701_: *mut crate::leanh::LeanObject,
    mut v_vals_4702_: *mut crate::leanh::LeanObject,
    mut v_i_4703_: *mut crate::leanh::LeanObject,
    mut v_k_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: u8 = 0;
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4705_ = lean_array_get_size(v_keys_4701_);
                v___x_4706_ = lean_nat_dec_lt(v_i_4703_, v___x_4705_);
                if v___x_4706_ == 0 {
                    crate::leanh::lean_dec(v_i_4703_);
                    v___x_4707_ = crate::leanh::lean_box(0);
                    return v___x_4707_;
                } else {
                    v_k_x27_4708_ = lean_array_fget_borrowed(v_keys_4701_, v_i_4703_);
                    v___x_4709_ = lean_name_eq(v_k_4704_, v_k_x27_4708_);
                    if v___x_4709_ == 0 {
                        v___x_4710_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4711_ = lean_nat_add(v_i_4703_, v___x_4710_);
                        crate::leanh::lean_dec(v_i_4703_);
                        v_i_4703_ = v___x_4711_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4713_ = lean_array_fget_borrowed(v_vals_4702_, v_i_4703_);
                        crate::leanh::lean_dec(v_i_4703_);
                        crate::leanh::lean_inc(v___x_4713_);
                        v___x_4714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4713_);
                        return v___x_4714_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4715_: *mut crate::leanh::LeanObject,
    mut v_vals_4716_: *mut crate::leanh::LeanObject,
    mut v_i_4717_: *mut crate::leanh::LeanObject,
    mut v_k_4718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4719_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4715_, v_vals_4716_, v_i_4717_, v_k_4718_);
    crate::leanh::lean_dec(v_k_4718_);
    crate::leanh::lean_dec_ref(v_vals_4716_);
    crate::leanh::lean_dec_ref(v_keys_4715_);
    return v_res_4719_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_4720_: usize = 0;
    let mut v___x_4721_: usize = 0;
    let mut v___x_4722_: usize = 0;
    v___x_4720_ = 5usize;
    v___x_4721_ = 1usize;
    v___x_4722_ = lean_usize_shift_left(v___x_4721_, v___x_4720_);
    return v___x_4722_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_4723_: usize = 0;
    let mut v___x_4724_: usize = 0;
    let mut v___x_4725_: usize = 0;
    v___x_4723_ = 1usize;
    v___x_4724_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_4725_ = lean_usize_sub(v___x_4724_, v___x_4723_);
    return v___x_4725_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(
    mut v_x_4726_: *mut crate::leanh::LeanObject,
    mut v_x_4727_: usize,
    mut v_x_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: usize = 0;
    let mut v___x_4732_: usize = 0;
    let mut v___x_4733_: usize = 0;
    let mut v_j_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: u8 = 0;
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: usize = 0;
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4726_) == 0 {
                    v_es_4729_ = crate::leanh::lean_ctor_get(v_x_4726_, 0);
                    v___x_4730_ = crate::leanh::lean_box(2);
                    v___x_4731_ = 5usize;
                    v___x_4732_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4733_ = lean_usize_land(v_x_4727_, v___x_4732_);
                    v_j_4734_ = lean_usize_to_nat(v___x_4733_);
                    v___x_4735_ = lean_array_get_borrowed(v___x_4730_, v_es_4729_, v_j_4734_);
                    crate::leanh::lean_dec(v_j_4734_);
                    match crate::leanh::lean_obj_tag(v___x_4735_) {
                        0 => {
                            v_key_4736_ = crate::leanh::lean_ctor_get(v___x_4735_, 0);
                            v_val_4737_ = crate::leanh::lean_ctor_get(v___x_4735_, 1);
                            v___x_4738_ = lean_name_eq(v_x_4728_, v_key_4736_);
                            if v___x_4738_ == 0 {
                                v___x_4739_ = crate::leanh::lean_box(0);
                                return v___x_4739_;
                            } else {
                                crate::leanh::lean_inc(v_val_4737_);
                                v___x_4740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4740_, 0, v_val_4737_);
                                return v___x_4740_;
                            }
                        }
                        1 => {
                            v_node_4741_ = crate::leanh::lean_ctor_get(v___x_4735_, 0);
                            v___x_4742_ = lean_usize_shift_right(v_x_4727_, v___x_4731_);
                            v_x_4726_ = v_node_4741_;
                            v_x_4727_ = v___x_4742_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4744_ = crate::leanh::lean_box(0);
                            return v___x_4744_;
                        }
                    }
                } else {
                    v_ks_4745_ = crate::leanh::lean_ctor_get(v_x_4726_, 0);
                    v_vs_4746_ = crate::leanh::lean_ctor_get(v_x_4726_, 1);
                    v___x_4747_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4748_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_4745_, v_vs_4746_, v___x_4747_, v_x_4728_);
                    return v___x_4748_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4749_: *mut crate::leanh::LeanObject,
    mut v_x_4750_: *mut crate::leanh::LeanObject,
    mut v_x_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_355__boxed_4752_: usize = 0;
    let mut v_res_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_355__boxed_4752_ = crate::leanh::lean_unbox_usize(v_x_4750_);
    crate::leanh::lean_dec(v_x_4750_);
    v_res_4753_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_4749_, v_x_355__boxed_4752_, v_x_4751_);
    crate::leanh::lean_dec(v_x_4751_);
    crate::leanh::lean_dec_ref(v_x_4749_);
    return v_res_4753_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: u64 = 0;
    v___x_4754_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4755_ = lean_uint64_of_nat(v___x_4754_);
    return v___x_4755_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(
    mut v_x_4756_: *mut crate::leanh::LeanObject,
    mut v_x_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4759_: u64 = 0;
    let mut v___x_4760_: usize = 0;
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u64 = 0;
    let mut v_hash_4763_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4757_) == 0 {
                    v___x_4762_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
                    v___y_4759_ = v___x_4762_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4763_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4757_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4759_ = v_hash_4763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4760_ = lean_uint64_to_usize(v___y_4759_);
                v___x_4761_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_4756_, v___x_4760_, v_x_4757_);
                return v___x_4761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___boxed(
    mut v_x_4764_: *mut crate::leanh::LeanObject,
    mut v_x_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(
            v_x_4764_, v_x_4765_,
        );
    crate::leanh::lean_dec(v_x_4765_);
    crate::leanh::lean_dec_ref(v_x_4764_);
    return v_res_4766_;
}
pub unsafe fn l_Lean_Meta_isEqnThm_x3f___redArg(
    mut v_thmName_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4770_ = lean_st_ref_get(v_a_4768_);
    v_env_4771_ = crate::leanh::lean_ctor_get(v___x_4770_, 0);
    crate::leanh::lean_inc_ref(v_env_4771_);
    crate::leanh::lean_dec(v___x_4770_);
    v___x_4772_ = l_Lean_Meta_eqnsExt;
    v_asyncMode_4773_ = crate::leanh::lean_ctor_get(v___x_4772_, 2);
    v___x_4774_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
    v___x_4775_ = crate::leanh::lean_box(0);
    v___x_4776_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4774_,
        v___x_4772_,
        v_env_4771_,
        v_asyncMode_4773_,
        v___x_4775_,
    );
    v___x_4777_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(
            v___x_4776_,
            v_thmName_4767_,
        );
    crate::leanh::lean_dec(v___x_4776_);
    v___x_4778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4778_, 0, v___x_4777_);
    return v___x_4778_;
}
pub unsafe fn l_Lean_Meta_isEqnThm_x3f___redArg___boxed(
    mut v_thmName_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
    mut v_a_4781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4782_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_4779_, v_a_4780_);
    crate::leanh::lean_dec(v_a_4780_);
    crate::leanh::lean_dec(v_thmName_4779_);
    return v_res_4782_;
}
pub unsafe fn l_Lean_Meta_isEqnThm_x3f(
    mut v_thmName_4783_: *mut crate::leanh::LeanObject,
    mut v_a_4784_: *mut crate::leanh::LeanObject,
    mut v_a_4785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4787_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_thmName_4783_, v_a_4785_);
    return v___x_4787_;
}
pub unsafe fn l_Lean_Meta_isEqnThm_x3f___boxed(
    mut v_thmName_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4792_ = l_Lean_Meta_isEqnThm_x3f(v_thmName_4788_, v_a_4789_, v_a_4790_);
    crate::leanh::lean_dec(v_a_4790_);
    crate::leanh::lean_dec_ref(v_a_4789_);
    crate::leanh::lean_dec(v_thmName_4788_);
    return v_res_4792_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(
    mut v_00_u03b2_4793_: *mut crate::leanh::LeanObject,
    mut v_x_4794_: *mut crate::leanh::LeanObject,
    mut v_x_4795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4796_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg(
            v_x_4794_, v_x_4795_,
        );
    return v___x_4796_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___boxed(
    mut v_00_u03b2_4797_: *mut crate::leanh::LeanObject,
    mut v_x_4798_: *mut crate::leanh::LeanObject,
    mut v_x_4799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4800_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0(
        v_00_u03b2_4797_,
        v_x_4798_,
        v_x_4799_,
    );
    crate::leanh::lean_dec(v_x_4799_);
    crate::leanh::lean_dec_ref(v_x_4798_);
    return v_res_4800_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(
    mut v_00_u03b2_4801_: *mut crate::leanh::LeanObject,
    mut v_x_4802_: *mut crate::leanh::LeanObject,
    mut v_x_4803_: usize,
    mut v_x_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4805_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg(v_x_4802_, v_x_4803_, v_x_4804_);
    return v___x_4805_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4806_: *mut crate::leanh::LeanObject,
    mut v_x_4807_: *mut crate::leanh::LeanObject,
    mut v_x_4808_: *mut crate::leanh::LeanObject,
    mut v_x_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_460__boxed_4810_: usize = 0;
    let mut v_res_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_460__boxed_4810_ = crate::leanh::lean_unbox_usize(v_x_4808_);
    crate::leanh::lean_dec(v_x_4808_);
    v_res_4811_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0(v_00_u03b2_4806_, v_x_4807_, v_x_460__boxed_4810_, v_x_4809_);
    crate::leanh::lean_dec(v_x_4809_);
    crate::leanh::lean_dec_ref(v_x_4807_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4812_: *mut crate::leanh::LeanObject,
    mut v_keys_4813_: *mut crate::leanh::LeanObject,
    mut v_vals_4814_: *mut crate::leanh::LeanObject,
    mut v_heq_4815_: *mut crate::leanh::LeanObject,
    mut v_i_4816_: *mut crate::leanh::LeanObject,
    mut v_k_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_4813_, v_vals_4814_, v_i_4816_, v_k_4817_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4819_: *mut crate::leanh::LeanObject,
    mut v_keys_4820_: *mut crate::leanh::LeanObject,
    mut v_vals_4821_: *mut crate::leanh::LeanObject,
    mut v_heq_4822_: *mut crate::leanh::LeanObject,
    mut v_i_4823_: *mut crate::leanh::LeanObject,
    mut v_k_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4819_, v_keys_4820_, v_vals_4821_, v_heq_4822_, v_i_4823_, v_k_4824_);
    crate::leanh::lean_dec(v_k_4824_);
    crate::leanh::lean_dec_ref(v_vals_4821_);
    crate::leanh::lean_dec_ref(v_keys_4820_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4826_: *mut crate::leanh::LeanObject,
    mut v_i_4827_: *mut crate::leanh::LeanObject,
    mut v_k_4828_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v_k_x27_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: u8 = 0;
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = lean_array_get_size(v_keys_4826_);
                v___x_4830_ = lean_nat_dec_lt(v_i_4827_, v___x_4829_);
                if v___x_4830_ == 0 {
                    crate::leanh::lean_dec(v_i_4827_);
                    return v___x_4830_;
                } else {
                    v_k_x27_4831_ = lean_array_fget_borrowed(v_keys_4826_, v_i_4827_);
                    v___x_4832_ = lean_name_eq(v_k_4828_, v_k_x27_4831_);
                    if v___x_4832_ == 0 {
                        v___x_4833_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4834_ = lean_nat_add(v_i_4827_, v___x_4833_);
                        crate::leanh::lean_dec(v_i_4827_);
                        v_i_4827_ = v___x_4834_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4827_);
                        return v___x_4832_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4836_: *mut crate::leanh::LeanObject,
    mut v_i_4837_: *mut crate::leanh::LeanObject,
    mut v_k_4838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4839_: u8 = 0;
    let mut v_r_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4839_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_4836_, v_i_4837_, v_k_4838_);
    crate::leanh::lean_dec(v_k_4838_);
    crate::leanh::lean_dec_ref(v_keys_4836_);
    v_r_4840_ = crate::leanh::lean_box((v_res_4839_) as usize);
    return v_r_4840_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(
    mut v_x_4841_: *mut crate::leanh::LeanObject,
    mut v_x_4842_: usize,
    mut v_x_4843_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: usize = 0;
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v_j_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v_node_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: usize = 0;
    let mut v___x_4856_: u8 = 0;
    let mut v_ks_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4841_) == 0 {
                    v_es_4844_ = crate::leanh::lean_ctor_get(v_x_4841_, 0);
                    v___x_4845_ = crate::leanh::lean_box(2);
                    v___x_4846_ = 5usize;
                    v___x_4847_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4848_ = lean_usize_land(v_x_4842_, v___x_4847_);
                    v_j_4849_ = lean_usize_to_nat(v___x_4848_);
                    v___x_4850_ = lean_array_get_borrowed(v___x_4845_, v_es_4844_, v_j_4849_);
                    crate::leanh::lean_dec(v_j_4849_);
                    match crate::leanh::lean_obj_tag(v___x_4850_) {
                        0 => {
                            v_key_4851_ = crate::leanh::lean_ctor_get(v___x_4850_, 0);
                            v___x_4852_ = lean_name_eq(v_x_4843_, v_key_4851_);
                            return v___x_4852_;
                        }
                        1 => {
                            v_node_4853_ = crate::leanh::lean_ctor_get(v___x_4850_, 0);
                            v___x_4854_ = lean_usize_shift_right(v_x_4842_, v___x_4846_);
                            v_x_4841_ = v_node_4853_;
                            v_x_4842_ = v___x_4854_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4856_ = 0;
                            return v___x_4856_;
                        }
                    }
                } else {
                    v_ks_4857_ = crate::leanh::lean_ctor_get(v_x_4841_, 0);
                    v___x_4858_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4859_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_ks_4857_, v___x_4858_, v_x_4843_);
                    return v___x_4859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg___boxed(
    mut v_x_4860_: *mut crate::leanh::LeanObject,
    mut v_x_4861_: *mut crate::leanh::LeanObject,
    mut v_x_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_335__boxed_4863_: usize = 0;
    let mut v_res_4864_: u8 = 0;
    let mut v_r_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_335__boxed_4863_ = crate::leanh::lean_unbox_usize(v_x_4861_);
    crate::leanh::lean_dec(v_x_4861_);
    v_res_4864_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_4860_, v_x_335__boxed_4863_, v_x_4862_);
    crate::leanh::lean_dec(v_x_4862_);
    crate::leanh::lean_dec_ref(v_x_4860_);
    v_r_4865_ = crate::leanh::lean_box((v_res_4864_) as usize);
    return v_r_4865_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(
    mut v_x_4866_: *mut crate::leanh::LeanObject,
    mut v_x_4867_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4869_: u64 = 0;
    let mut v___x_4870_: usize = 0;
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: u64 = 0;
    let mut v_hash_4873_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4867_) == 0 {
                    v___x_4872_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
                    v___y_4869_ = v___x_4872_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4873_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4867_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4869_ = v_hash_4873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4870_ = lean_uint64_to_usize(v___y_4869_);
                v___x_4871_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_4866_, v___x_4870_, v_x_4867_);
                return v___x_4871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg___boxed(
    mut v_x_4874_: *mut crate::leanh::LeanObject,
    mut v_x_4875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4876_: u8 = 0;
    let mut v_r_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4876_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(
        v_x_4874_, v_x_4875_,
    );
    crate::leanh::lean_dec(v_x_4875_);
    crate::leanh::lean_dec_ref(v_x_4874_);
    v_r_4877_ = crate::leanh::lean_box((v_res_4876_) as usize);
    return v_r_4877_;
}
pub unsafe fn l_Lean_Meta_isEqnThm___redArg(
    mut v_thmName_4878_: *mut crate::leanh::LeanObject,
    mut v_a_4879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: u8 = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4881_ = lean_st_ref_get(v_a_4879_);
    v_env_4882_ = crate::leanh::lean_ctor_get(v___x_4881_, 0);
    crate::leanh::lean_inc_ref(v_env_4882_);
    crate::leanh::lean_dec(v___x_4881_);
    v___x_4883_ = l_Lean_Meta_eqnsExt;
    v_asyncMode_4884_ = crate::leanh::lean_ctor_get(v___x_4883_, 2);
    v___x_4885_ = l_Lean_Meta_instInhabitedEqnsExtState_default;
    v___x_4886_ = crate::leanh::lean_box(0);
    v___x_4887_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4885_,
        v___x_4883_,
        v_env_4882_,
        v_asyncMode_4884_,
        v___x_4886_,
    );
    v___x_4888_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(
        v___x_4887_,
        v_thmName_4878_,
    );
    crate::leanh::lean_dec(v___x_4887_);
    v___x_4889_ = crate::leanh::lean_box((v___x_4888_) as usize);
    v___x_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4890_, 0, v___x_4889_);
    return v___x_4890_;
}
pub unsafe fn l_Lean_Meta_isEqnThm___redArg___boxed(
    mut v_thmName_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v_a_4893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4894_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_4891_, v_a_4892_);
    crate::leanh::lean_dec(v_a_4892_);
    crate::leanh::lean_dec(v_thmName_4891_);
    return v_res_4894_;
}
pub unsafe fn l_Lean_Meta_isEqnThm(
    mut v_thmName_4895_: *mut crate::leanh::LeanObject,
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_a_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4899_ = l_Lean_Meta_isEqnThm___redArg(v_thmName_4895_, v_a_4897_);
    return v___x_4899_;
}
pub unsafe fn l_Lean_Meta_isEqnThm___boxed(
    mut v_thmName_4900_: *mut crate::leanh::LeanObject,
    mut v_a_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4904_ = l_Lean_Meta_isEqnThm(v_thmName_4900_, v_a_4901_, v_a_4902_);
    crate::leanh::lean_dec(v_a_4902_);
    crate::leanh::lean_dec_ref(v_a_4901_);
    crate::leanh::lean_dec(v_thmName_4900_);
    return v_res_4904_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(
    mut v_00_u03b2_4905_: *mut crate::leanh::LeanObject,
    mut v_x_4906_: *mut crate::leanh::LeanObject,
    mut v_x_4907_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4908_: u8 = 0;
    v___x_4908_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___redArg(
        v_x_4906_, v_x_4907_,
    );
    return v___x_4908_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0___boxed(
    mut v_00_u03b2_4909_: *mut crate::leanh::LeanObject,
    mut v_x_4910_: *mut crate::leanh::LeanObject,
    mut v_x_4911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4912_: u8 = 0;
    let mut v_r_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4912_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0(
        v_00_u03b2_4909_,
        v_x_4910_,
        v_x_4911_,
    );
    crate::leanh::lean_dec(v_x_4911_);
    crate::leanh::lean_dec_ref(v_x_4910_);
    v_r_4913_ = crate::leanh::lean_box((v_res_4912_) as usize);
    return v_r_4913_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(
    mut v_00_u03b2_4914_: *mut crate::leanh::LeanObject,
    mut v_x_4915_: *mut crate::leanh::LeanObject,
    mut v_x_4916_: usize,
    mut v_x_4917_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4918_: u8 = 0;
    v___x_4918_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___redArg(v_x_4915_, v_x_4916_, v_x_4917_);
    return v___x_4918_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0___boxed(
    mut v_00_u03b2_4919_: *mut crate::leanh::LeanObject,
    mut v_x_4920_: *mut crate::leanh::LeanObject,
    mut v_x_4921_: *mut crate::leanh::LeanObject,
    mut v_x_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_429__boxed_4923_: usize = 0;
    let mut v_res_4924_: u8 = 0;
    let mut v_r_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_429__boxed_4923_ = crate::leanh::lean_unbox_usize(v_x_4921_);
    crate::leanh::lean_dec(v_x_4921_);
    v_res_4924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0(v_00_u03b2_4919_, v_x_4920_, v_x_429__boxed_4923_, v_x_4922_);
    crate::leanh::lean_dec(v_x_4922_);
    crate::leanh::lean_dec_ref(v_x_4920_);
    v_r_4925_ = crate::leanh::lean_box((v_res_4924_) as usize);
    return v_r_4925_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4926_: *mut crate::leanh::LeanObject,
    mut v_keys_4927_: *mut crate::leanh::LeanObject,
    mut v_vals_4928_: *mut crate::leanh::LeanObject,
    mut v_heq_4929_: *mut crate::leanh::LeanObject,
    mut v_i_4930_: *mut crate::leanh::LeanObject,
    mut v_k_4931_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4932_: u8 = 0;
    v___x_4932_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___redArg(v_keys_4927_, v_i_4930_, v_k_4931_);
    return v___x_4932_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4933_: *mut crate::leanh::LeanObject,
    mut v_keys_4934_: *mut crate::leanh::LeanObject,
    mut v_vals_4935_: *mut crate::leanh::LeanObject,
    mut v_heq_4936_: *mut crate::leanh::LeanObject,
    mut v_i_4937_: *mut crate::leanh::LeanObject,
    mut v_k_4938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4939_: u8 = 0;
    let mut v_r_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4939_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_isEqnThm_spec__0_spec__0_spec__1(v_00_u03b2_4933_, v_keys_4934_, v_vals_4935_, v_heq_4936_, v_i_4937_, v_k_4938_);
    crate::leanh::lean_dec(v_k_4938_);
    crate::leanh::lean_dec_ref(v_vals_4935_);
    crate::leanh::lean_dec_ref(v_keys_4934_);
    v_r_4940_ = crate::leanh::lean_box((v_res_4939_) as usize);
    return v_r_4940_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_4941_: *mut crate::leanh::LeanObject,
    mut v_x_4942_: *mut crate::leanh::LeanObject,
    mut v_x_4943_: *mut crate::leanh::LeanObject,
    mut v_x_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: u8 = 0;
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: u8 = 0;
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4945_ = crate::leanh::lean_ctor_get(v_x_4941_, 0);
                v_vs_4946_ = crate::leanh::lean_ctor_get(v_x_4941_, 1);
                v_isSharedCheck_4970_ = (!crate::leanh::lean_is_exclusive(v_x_4941_)) as u8;
                if v_isSharedCheck_4970_ == 0 {
                    v___x_4948_ = v_x_4941_;
                    v_isShared_4949_ = v_isSharedCheck_4970_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4946_);
                    crate::leanh::lean_inc(v_ks_4945_);
                    crate::leanh::lean_dec(v_x_4941_);
                    v___x_4948_ = crate::leanh::lean_box(0);
                    v_isShared_4949_ = v_isSharedCheck_4970_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4950_ = lean_array_get_size(v_ks_4945_);
                v___x_4951_ = lean_nat_dec_lt(v_x_4942_, v___x_4950_);
                if v___x_4951_ == 0 {
                    crate::leanh::lean_dec(v_x_4942_);
                    v___x_4952_ = lean_array_push(v_ks_4945_, v_x_4943_);
                    v___x_4953_ = lean_array_push(v_vs_4946_, v_x_4944_);
                    if v_isShared_4949_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4948_, 1, v___x_4953_);
                        crate::leanh::lean_ctor_set(v___x_4948_, 0, v___x_4952_);
                        v___x_4955_ = v___x_4948_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4956_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4952_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 1, v___x_4953_);
                        v___x_4955_ = v_reuseFailAlloc_4956_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4957_ = lean_array_fget_borrowed(v_ks_4945_, v_x_4942_);
                    v___x_4958_ = lean_name_eq(v_x_4943_, v_k_x27_4957_);
                    if v___x_4958_ == 0 {
                        if v_isShared_4949_ == 0 {
                            v___x_4960_ = v___x_4948_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4964_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_ks_4945_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 1, v_vs_4946_);
                            v___x_4960_ = v_reuseFailAlloc_4964_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4965_ = lean_array_fset(v_ks_4945_, v_x_4942_, v_x_4943_);
                        v___x_4966_ = lean_array_fset(v_vs_4946_, v_x_4942_, v_x_4944_);
                        crate::leanh::lean_dec(v_x_4942_);
                        if v_isShared_4949_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4948_, 1, v___x_4966_);
                            crate::leanh::lean_ctor_set(v___x_4948_, 0, v___x_4965_);
                            v___x_4968_ = v___x_4948_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4969_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4965_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4969_, 1, v___x_4966_);
                            v___x_4968_ = v_reuseFailAlloc_4969_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4955_;
            }
            3 => {
                v___x_4961_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4962_ = lean_nat_add(v_x_4942_, v___x_4961_);
                crate::leanh::lean_dec(v_x_4942_);
                v_x_4941_ = v___x_4960_;
                v_x_4942_ = v___x_4962_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(
    mut v_n_4971_: *mut crate::leanh::LeanObject,
    mut v_k_4972_: *mut crate::leanh::LeanObject,
    mut v_v_4973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4974_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4975_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_n_4971_, v___x_4974_, v_k_4972_, v_v_4973_);
    return v___x_4975_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4976_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(
    mut v_x_4977_: *mut crate::leanh::LeanObject,
    mut v_x_4978_: usize,
    mut v_x_4979_: usize,
    mut v_x_4980_: *mut crate::leanh::LeanObject,
    mut v_x_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: usize = 0;
    let mut v___x_4984_: usize = 0;
    let mut v___x_4985_: usize = 0;
    let mut v___x_4986_: usize = 0;
    let mut v_j_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v_v_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5013_: u8 = 0;
    let mut v_node_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5017_: u8 = 0;
    let mut v___x_5018_: usize = 0;
    let mut v___x_5019_: usize = 0;
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5024_: u8 = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5026_: u8 = 0;
    let mut v_unused_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5037_: u8 = 0;
    let mut v_ks_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: usize = 0;
    let mut v___x_5044_: u8 = 0;
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: u8 = 0;
    let mut v_reuseFailAlloc_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4977_) == 0 {
                    v_es_4982_ = crate::leanh::lean_ctor_get(v_x_4977_, 0);
                    v___x_4983_ = 5usize;
                    v___x_4984_ = 1usize;
                    v___x_4985_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_4986_ = lean_usize_land(v_x_4978_, v___x_4985_);
                    v_j_4987_ = lean_usize_to_nat(v___x_4986_);
                    v___x_4988_ = lean_array_get_size(v_es_4982_);
                    v___x_4989_ = lean_nat_dec_lt(v_j_4987_, v___x_4988_);
                    if v___x_4989_ == 0 {
                        crate::leanh::lean_dec(v_j_4987_);
                        crate::leanh::lean_dec(v_x_4981_);
                        crate::leanh::lean_dec(v_x_4980_);
                        return v_x_4977_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4982_);
                        v_isSharedCheck_5026_ = (!crate::leanh::lean_is_exclusive(v_x_4977_)) as u8;
                        if v_isSharedCheck_5026_ == 0 {
                            v_unused_5027_ = crate::leanh::lean_ctor_get(v_x_4977_, 0);
                            crate::leanh::lean_dec(v_unused_5027_);
                            v___x_4991_ = v_x_4977_;
                            v_isShared_4992_ = v_isSharedCheck_5026_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4977_);
                            v___x_4991_ = crate::leanh::lean_box(0);
                            v_isShared_4992_ = v_isSharedCheck_5026_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5028_ = crate::leanh::lean_ctor_get(v_x_4977_, 0);
                    v_vs_5029_ = crate::leanh::lean_ctor_get(v_x_4977_, 1);
                    v_isSharedCheck_5049_ = (!crate::leanh::lean_is_exclusive(v_x_4977_)) as u8;
                    if v_isSharedCheck_5049_ == 0 {
                        v___x_5031_ = v_x_4977_;
                        v_isShared_5032_ = v_isSharedCheck_5049_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5029_);
                        crate::leanh::lean_inc(v_ks_5028_);
                        crate::leanh::lean_dec(v_x_4977_);
                        v___x_5031_ = crate::leanh::lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5049_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4993_ = lean_array_fget(v_es_4982_, v_j_4987_);
                v___x_4994_ = crate::leanh::lean_box(0);
                v_xs_x27_4995_ = lean_array_fset(v_es_4982_, v_j_4987_, v___x_4994_);
                match crate::leanh::lean_obj_tag(v_v_4993_) {
                    0 => {
                        v_key_5002_ = crate::leanh::lean_ctor_get(v_v_4993_, 0);
                        v_val_5003_ = crate::leanh::lean_ctor_get(v_v_4993_, 1);
                        v_isSharedCheck_5013_ = (!crate::leanh::lean_is_exclusive(v_v_4993_)) as u8;
                        if v_isSharedCheck_5013_ == 0 {
                            v___x_5005_ = v_v_4993_;
                            v_isShared_5006_ = v_isSharedCheck_5013_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5003_);
                            crate::leanh::lean_inc(v_key_5002_);
                            crate::leanh::lean_dec(v_v_4993_);
                            v___x_5005_ = crate::leanh::lean_box(0);
                            v_isShared_5006_ = v_isSharedCheck_5013_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5014_ = crate::leanh::lean_ctor_get(v_v_4993_, 0);
                        v_isSharedCheck_5024_ = (!crate::leanh::lean_is_exclusive(v_v_4993_)) as u8;
                        if v_isSharedCheck_5024_ == 0 {
                            v___x_5016_ = v_v_4993_;
                            v_isShared_5017_ = v_isSharedCheck_5024_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5014_);
                            crate::leanh::lean_dec(v_v_4993_);
                            v___x_5016_ = crate::leanh::lean_box(0);
                            v_isShared_5017_ = v_isSharedCheck_5024_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5025_, 0, v_x_4980_);
                        crate::leanh::lean_ctor_set(v___x_5025_, 1, v_x_4981_);
                        v___y_4997_ = v___x_5025_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4998_ = lean_array_fset(v_xs_x27_4995_, v_j_4987_, v___y_4997_);
                crate::leanh::lean_dec(v_j_4987_);
                if v_isShared_4992_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4991_, 0, v___x_4998_);
                    v___x_5000_ = v___x_4991_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5000_;
            }
            4 => {
                v___x_5007_ = lean_name_eq(v_x_4980_, v_key_5002_);
                if v___x_5007_ == 0 {
                    crate::leanh::lean_del_object(v___x_5005_);
                    v___x_5008_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5002_,
                        v_val_5003_,
                        v_x_4980_,
                        v_x_4981_,
                    );
                    v___x_5009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5009_, 0, v___x_5008_);
                    v___y_4997_ = v___x_5009_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5003_);
                    crate::leanh::lean_dec(v_key_5002_);
                    if v_isShared_5006_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5005_, 1, v_x_4981_);
                        crate::leanh::lean_ctor_set(v___x_5005_, 0, v_x_4980_);
                        v___x_5011_ = v___x_5005_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5012_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_x_4980_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5012_, 1, v_x_4981_);
                        v___x_5011_ = v_reuseFailAlloc_5012_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4997_ = v___x_5011_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5018_ = lean_usize_shift_right(v_x_4978_, v___x_4983_);
                v___x_5019_ = lean_usize_add(v_x_4979_, v___x_4984_);
                v___x_5020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_node_5014_, v___x_5018_, v___x_5019_, v_x_4980_, v_x_4981_);
                if v_isShared_5017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5016_, 0, v___x_5020_);
                    v___x_5022_ = v___x_5016_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5020_);
                    v___x_5022_ = v_reuseFailAlloc_5023_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4997_ = v___x_5022_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_ks_5028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 1, v_vs_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5048_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5035_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v___x_5034_, v_x_4980_, v_x_4981_);
                v___x_5043_ = 7usize;
                v___x_5044_ = lean_usize_dec_le(v___x_5043_, v_x_4979_);
                if v___x_5044_ == 0 {
                    v___x_5045_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5035_);
                    v___x_5046_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5047_ = lean_nat_dec_lt(v___x_5045_, v___x_5046_);
                    crate::leanh::lean_dec(v___x_5045_);
                    v___y_5037_ = v___x_5047_;
                    state = 10;
                    continue;
                } else {
                    v___y_5037_ = v___x_5044_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5037_ == 0 {
                    v_ks_5038_ = crate::leanh::lean_ctor_get(v_newNode_5035_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5038_);
                    v_vs_5039_ = crate::leanh::lean_ctor_get(v_newNode_5035_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5039_);
                    crate::leanh::lean_dec_ref(v_newNode_5035_);
                    v___x_5040_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___closed__0);
                    v___x_5042_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_x_4979_, v_ks_5038_, v_vs_5039_, v___x_5040_, v___x_5041_);
                    crate::leanh::lean_dec_ref(v_vs_5039_);
                    crate::leanh::lean_dec_ref(v_ks_5038_);
                    return v___x_5042_;
                } else {
                    return v_newNode_5035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(
    mut v_depth_5050_: usize,
    mut v_keys_5051_: *mut crate::leanh::LeanObject,
    mut v_vals_5052_: *mut crate::leanh::LeanObject,
    mut v_i_5053_: *mut crate::leanh::LeanObject,
    mut v_entries_5054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: u8 = 0;
    let mut v_k_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5060_: u64 = 0;
    let mut v_h_5061_: usize = 0;
    let mut v___x_5062_: usize = 0;
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: usize = 0;
    let mut v___x_5065_: usize = 0;
    let mut v___x_5066_: usize = 0;
    let mut v_h_5067_: usize = 0;
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u64 = 0;
    let mut v_hash_5072_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5055_ = lean_array_get_size(v_keys_5051_);
                v___x_5056_ = lean_nat_dec_lt(v_i_5053_, v___x_5055_);
                if v___x_5056_ == 0 {
                    crate::leanh::lean_dec(v_i_5053_);
                    return v_entries_5054_;
                } else {
                    v_k_5057_ = lean_array_fget_borrowed(v_keys_5051_, v_i_5053_);
                    v_v_5058_ = lean_array_fget_borrowed(v_vals_5052_, v_i_5053_);
                    if crate::leanh::lean_obj_tag(v_k_5057_) == 0 {
                        v___x_5071_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
                        v___y_5060_ = v___x_5071_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_5072_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_5057_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_5060_ = v_hash_5072_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_5061_ = lean_uint64_to_usize(v___y_5060_);
                v___x_5062_ = 5usize;
                v___x_5063_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5064_ = 1usize;
                v___x_5065_ = lean_usize_sub(v_depth_5050_, v___x_5064_);
                v___x_5066_ = lean_usize_mul(v___x_5062_, v___x_5065_);
                v_h_5067_ = lean_usize_shift_right(v_h_5061_, v___x_5066_);
                v___x_5068_ = lean_nat_add(v_i_5053_, v___x_5063_);
                crate::leanh::lean_dec(v_i_5053_);
                crate::leanh::lean_inc(v_v_5058_);
                crate::leanh::lean_inc(v_k_5057_);
                v___x_5069_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_entries_5054_, v_h_5067_, v_depth_5050_, v_k_5057_, v_v_5058_);
                v_i_5053_ = v___x_5068_;
                v_entries_5054_ = v___x_5069_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_5073_: *mut crate::leanh::LeanObject,
    mut v_keys_5074_: *mut crate::leanh::LeanObject,
    mut v_vals_5075_: *mut crate::leanh::LeanObject,
    mut v_i_5076_: *mut crate::leanh::LeanObject,
    mut v_entries_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5078_: usize = 0;
    let mut v_res_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5078_ = crate::leanh::lean_unbox_usize(v_depth_5073_);
    crate::leanh::lean_dec(v_depth_5073_);
    v_res_5079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_boxed_5078_, v_keys_5074_, v_vals_5075_, v_i_5076_, v_entries_5077_);
    crate::leanh::lean_dec_ref(v_vals_5075_);
    crate::leanh::lean_dec_ref(v_keys_5074_);
    return v_res_5079_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg___boxed(
    mut v_x_5080_: *mut crate::leanh::LeanObject,
    mut v_x_5081_: *mut crate::leanh::LeanObject,
    mut v_x_5082_: *mut crate::leanh::LeanObject,
    mut v_x_5083_: *mut crate::leanh::LeanObject,
    mut v_x_5084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_634__boxed_5085_: usize = 0;
    let mut v_x_635__boxed_5086_: usize = 0;
    let mut v_res_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_634__boxed_5085_ = crate::leanh::lean_unbox_usize(v_x_5081_);
    crate::leanh::lean_dec(v_x_5081_);
    v_x_635__boxed_5086_ = crate::leanh::lean_unbox_usize(v_x_5082_);
    crate::leanh::lean_dec(v_x_5082_);
    v_res_5087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_5080_, v_x_634__boxed_5085_, v_x_635__boxed_5086_, v_x_5083_, v_x_5084_);
    return v_res_5087_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(
    mut v_x_5088_: *mut crate::leanh::LeanObject,
    mut v_x_5089_: *mut crate::leanh::LeanObject,
    mut v_x_5090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5092_: u64 = 0;
    let mut v___x_5093_: usize = 0;
    let mut v___x_5094_: usize = 0;
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: u64 = 0;
    let mut v_hash_5097_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5089_) == 0 {
                    v___x_5096_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_isEqnThm_x3f_spec__0___redArg___closed__0);
                    v___y_5092_ = v___x_5096_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5097_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_5089_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5092_ = v_hash_5097_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5093_ = lean_uint64_to_usize(v___y_5092_);
                v___x_5094_ = 1usize;
                v___x_5095_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_5088_, v___x_5093_, v___x_5094_, v_x_5089_, v_x_5090_);
                return v___x_5095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(
    mut v_declName_5098_: *mut crate::leanh::LeanObject,
    mut v_as_5099_: *mut crate::leanh::LeanObject,
    mut v_i_5100_: usize,
    mut v_stop_5101_: usize,
    mut v_b_5102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: usize = 0;
    let mut v___x_5107_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5103_ = lean_usize_dec_eq(v_i_5100_, v_stop_5101_);
                if v___x_5103_ == 0 {
                    v___x_5104_ = lean_array_uget_borrowed(v_as_5099_, v_i_5100_);
                    crate::leanh::lean_inc(v_declName_5098_);
                    crate::leanh::lean_inc(v___x_5104_);
                    v___x_5105_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_b_5102_, v___x_5104_, v_declName_5098_);
                    v___x_5106_ = 1usize;
                    v___x_5107_ = lean_usize_add(v_i_5100_, v___x_5106_);
                    v_i_5100_ = v___x_5107_;
                    v_b_5102_ = v___x_5105_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_declName_5098_);
                    return v_b_5102_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1___boxed(
    mut v_declName_5109_: *mut crate::leanh::LeanObject,
    mut v_as_5110_: *mut crate::leanh::LeanObject,
    mut v_i_5111_: *mut crate::leanh::LeanObject,
    mut v_stop_5112_: *mut crate::leanh::LeanObject,
    mut v_b_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5114_: usize = 0;
    let mut v_stop_boxed_5115_: usize = 0;
    let mut v_res_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5114_ = crate::leanh::lean_unbox_usize(v_i_5111_);
    crate::leanh::lean_dec(v_i_5111_);
    v_stop_boxed_5115_ = crate::leanh::lean_unbox_usize(v_stop_5112_);
    crate::leanh::lean_dec(v_stop_5112_);
    v_res_5116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_5109_, v_as_5110_, v_i_boxed_5114_, v_stop_boxed_5115_, v_b_5113_);
    crate::leanh::lean_dec_ref(v_as_5110_);
    return v_res_5116_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(
    mut v_eqThms_5117_: *mut crate::leanh::LeanObject,
    mut v_declName_5118_: *mut crate::leanh::LeanObject,
    mut v_s_5119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: u8 = 0;
    v___x_5120_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5121_ = lean_array_get_size(v_eqThms_5117_);
    v___x_5122_ = lean_nat_dec_lt(v___x_5120_, v___x_5121_);
    if v___x_5122_ == 0 {
        crate::leanh::lean_dec(v_declName_5118_);
        return v_s_5119_;
    } else {
        let mut v___x_5123_: u8 = 0;
        v___x_5123_ = lean_nat_dec_le(v___x_5121_, v___x_5121_);
        if v___x_5123_ == 0 {
            if v___x_5122_ == 0 {
                crate::leanh::lean_dec(v_declName_5118_);
                return v_s_5119_;
            } else {
                let mut v___x_5124_: usize = 0;
                let mut v___x_5125_: usize = 0;
                let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5124_ = 0usize;
                v___x_5125_ = lean_usize_of_nat(v___x_5121_);
                v___x_5126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_5118_, v_eqThms_5117_, v___x_5124_, v___x_5125_, v_s_5119_);
                return v___x_5126_;
            }
        } else {
            let mut v___x_5127_: usize = 0;
            let mut v___x_5128_: usize = 0;
            let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5127_ = 0usize;
            v___x_5128_ = lean_usize_of_nat(v___x_5121_);
            v___x_5129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__1(v_declName_5118_, v_eqThms_5117_, v___x_5127_, v___x_5128_, v_s_5119_);
            return v___x_5129_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(
    mut v_eqThms_5130_: *mut crate::leanh::LeanObject,
    mut v_declName_5131_: *mut crate::leanh::LeanObject,
    mut v_s_5132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5133_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(
        v_eqThms_5130_,
        v_declName_5131_,
        v_s_5132_,
    );
    crate::leanh::lean_dec_ref(v_eqThms_5130_);
    return v_res_5133_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(
    mut v_declName_5134_: *mut crate::leanh::LeanObject,
    mut v_eqThms_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5162_: u8 = 0;
    let mut v_unused_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5138_ = lean_st_ref_take(v_a_5136_);
                v_env_5139_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                v_nextMacroScope_5140_ = crate::leanh::lean_ctor_get(v___x_5138_, 1);
                v_ngen_5141_ = crate::leanh::lean_ctor_get(v___x_5138_, 2);
                v_auxDeclNGen_5142_ = crate::leanh::lean_ctor_get(v___x_5138_, 3);
                v_traceState_5143_ = crate::leanh::lean_ctor_get(v___x_5138_, 4);
                v_messages_5144_ = crate::leanh::lean_ctor_get(v___x_5138_, 6);
                v_infoState_5145_ = crate::leanh::lean_ctor_get(v___x_5138_, 7);
                v_snapshotTasks_5146_ = crate::leanh::lean_ctor_get(v___x_5138_, 8);
                v_isSharedCheck_5162_ = (!crate::leanh::lean_is_exclusive(v___x_5138_)) as u8;
                if v_isSharedCheck_5162_ == 0 {
                    v_unused_5163_ = crate::leanh::lean_ctor_get(v___x_5138_, 5);
                    crate::leanh::lean_dec(v_unused_5163_);
                    v___x_5148_ = v___x_5138_;
                    v_isShared_5149_ = v_isSharedCheck_5162_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5146_);
                    crate::leanh::lean_inc(v_infoState_5145_);
                    crate::leanh::lean_inc(v_messages_5144_);
                    crate::leanh::lean_inc(v_traceState_5143_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5142_);
                    crate::leanh::lean_inc(v_ngen_5141_);
                    crate::leanh::lean_inc(v_nextMacroScope_5140_);
                    crate::leanh::lean_inc(v_env_5139_);
                    crate::leanh::lean_dec(v___x_5138_);
                    v___x_5148_ = crate::leanh::lean_box(0);
                    v_isShared_5149_ = v_isSharedCheck_5162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5150_ = l_Lean_Meta_eqnsExt;
                v_asyncMode_5151_ = crate::leanh::lean_ctor_get(v___x_5150_, 2);
                v___f_5152_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_5152_, 0, v_eqThms_5135_);
                crate::leanh::lean_closure_set(v___f_5152_, 1, v_declName_5134_);
                v___x_5153_ = crate::leanh::lean_box(0);
                v___x_5154_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_5150_,
                    v_env_5139_,
                    v___f_5152_,
                    v_asyncMode_5151_,
                    v___x_5153_,
                );
                v___x_5155_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2_once),
                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__2,
                );
                if v_isShared_5149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5148_, 5, v___x_5155_);
                    crate::leanh::lean_ctor_set(v___x_5148_, 0, v___x_5154_);
                    v___x_5157_ = v___x_5148_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5161_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 0, v___x_5154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 1, v_nextMacroScope_5140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 2, v_ngen_5141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 3, v_auxDeclNGen_5142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 4, v_traceState_5143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 5, v___x_5155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 6, v_messages_5144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 7, v_infoState_5145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5161_, 8, v_snapshotTasks_5146_);
                    v___x_5157_ = v_reuseFailAlloc_5161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5158_ = lean_st_ref_set(v_a_5136_, v___x_5157_);
                v___x_5159_ = crate::leanh::lean_box(0);
                v___x_5160_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5159_);
                return v___x_5160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(
    mut v_declName_5164_: *mut crate::leanh::LeanObject,
    mut v_eqThms_5165_: *mut crate::leanh::LeanObject,
    mut v_a_5166_: *mut crate::leanh::LeanObject,
    mut v_a_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(
        v_declName_5164_,
        v_eqThms_5165_,
        v_a_5166_,
    );
    crate::leanh::lean_dec(v_a_5166_);
    return v_res_5168_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(
    mut v_declName_5169_: *mut crate::leanh::LeanObject,
    mut v_eqThms_5170_: *mut crate::leanh::LeanObject,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
    mut v_a_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5174_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(
        v_declName_5169_,
        v_eqThms_5170_,
        v_a_5172_,
    );
    return v___x_5174_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(
    mut v_declName_5175_: *mut crate::leanh::LeanObject,
    mut v_eqThms_5176_: *mut crate::leanh::LeanObject,
    mut v_a_5177_: *mut crate::leanh::LeanObject,
    mut v_a_5178_: *mut crate::leanh::LeanObject,
    mut v_a_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5180_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(
        v_declName_5175_,
        v_eqThms_5176_,
        v_a_5177_,
        v_a_5178_,
    );
    crate::leanh::lean_dec(v_a_5178_);
    crate::leanh::lean_dec_ref(v_a_5177_);
    return v_res_5180_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(
    mut v_00_u03b2_5181_: *mut crate::leanh::LeanObject,
    mut v_x_5182_: *mut crate::leanh::LeanObject,
    mut v_x_5183_: *mut crate::leanh::LeanObject,
    mut v_x_5184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5185_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___redArg(v_x_5182_, v_x_5183_, v_x_5184_);
    return v___x_5185_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(
    mut v_00_u03b2_5186_: *mut crate::leanh::LeanObject,
    mut v_x_5187_: *mut crate::leanh::LeanObject,
    mut v_x_5188_: usize,
    mut v_x_5189_: usize,
    mut v_x_5190_: *mut crate::leanh::LeanObject,
    mut v_x_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___redArg(v_x_5187_, v_x_5188_, v_x_5189_, v_x_5190_, v_x_5191_);
    return v___x_5192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0___boxed(
    mut v_00_u03b2_5193_: *mut crate::leanh::LeanObject,
    mut v_x_5194_: *mut crate::leanh::LeanObject,
    mut v_x_5195_: *mut crate::leanh::LeanObject,
    mut v_x_5196_: *mut crate::leanh::LeanObject,
    mut v_x_5197_: *mut crate::leanh::LeanObject,
    mut v_x_5198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_903__boxed_5199_: usize = 0;
    let mut v_x_904__boxed_5200_: usize = 0;
    let mut v_res_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_903__boxed_5199_ = crate::leanh::lean_unbox_usize(v_x_5195_);
    crate::leanh::lean_dec(v_x_5195_);
    v_x_904__boxed_5200_ = crate::leanh::lean_unbox_usize(v_x_5196_);
    crate::leanh::lean_dec(v_x_5196_);
    v_res_5201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0(v_00_u03b2_5193_, v_x_5194_, v_x_903__boxed_5199_, v_x_904__boxed_5200_, v_x_5197_, v_x_5198_);
    return v_res_5201_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5202_: *mut crate::leanh::LeanObject,
    mut v_n_5203_: *mut crate::leanh::LeanObject,
    mut v_k_5204_: *mut crate::leanh::LeanObject,
    mut v_v_5205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1___redArg(v_n_5203_, v_k_5204_, v_v_5205_);
    return v___x_5206_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5207_: *mut crate::leanh::LeanObject,
    mut v_depth_5208_: usize,
    mut v_keys_5209_: *mut crate::leanh::LeanObject,
    mut v_vals_5210_: *mut crate::leanh::LeanObject,
    mut v_heq_5211_: *mut crate::leanh::LeanObject,
    mut v_i_5212_: *mut crate::leanh::LeanObject,
    mut v_entries_5213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___redArg(v_depth_5208_, v_keys_5209_, v_vals_5210_, v_i_5212_, v_entries_5213_);
    return v___x_5214_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5215_: *mut crate::leanh::LeanObject,
    mut v_depth_5216_: *mut crate::leanh::LeanObject,
    mut v_keys_5217_: *mut crate::leanh::LeanObject,
    mut v_vals_5218_: *mut crate::leanh::LeanObject,
    mut v_heq_5219_: *mut crate::leanh::LeanObject,
    mut v_i_5220_: *mut crate::leanh::LeanObject,
    mut v_entries_5221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5222_: usize = 0;
    let mut v_res_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5222_ = crate::leanh::lean_unbox_usize(v_depth_5216_);
    crate::leanh::lean_dec(v_depth_5216_);
    v_res_5223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__2(v_00_u03b2_5215_, v_depth_boxed_5222_, v_keys_5217_, v_vals_5218_, v_heq_5219_, v_i_5220_, v_entries_5221_);
    crate::leanh::lean_dec_ref(v_vals_5218_);
    crate::leanh::lean_dec_ref(v_keys_5217_);
    return v_res_5223_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5224_: *mut crate::leanh::LeanObject,
    mut v_x_5225_: *mut crate::leanh::LeanObject,
    mut v_x_5226_: *mut crate::leanh::LeanObject,
    mut v_x_5227_: *mut crate::leanh::LeanObject,
    mut v_x_5228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0_spec__0_spec__1_spec__3___redArg(v_x_5225_, v_x_5226_, v_x_5227_, v_x_5228_);
    return v___x_5229_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(
    mut v_declName_5230_: *mut crate::leanh::LeanObject,
    mut v_env_5231_: *mut crate::leanh::LeanObject,
    mut v_idx_5232_: *mut crate::leanh::LeanObject,
    mut v_eqs_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextEq_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5235_ = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
                v___x_5236_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5237_ = lean_nat_add(v_idx_5232_, v___x_5236_);
                crate::leanh::lean_dec(v_idx_5232_);
                crate::leanh::lean_inc(v___x_5237_);
                v___x_5238_ = l_Nat_reprFast(v___x_5237_);
                v___x_5239_ = lean_string_append(v___x_5235_, v___x_5238_);
                crate::leanh::lean_dec_ref(v___x_5238_);
                crate::leanh::lean_inc(v_declName_5230_);
                crate::leanh::lean_inc_ref(v_env_5231_);
                v_nextEq_5240_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_5231_, v_declName_5230_, v___x_5239_);
                v___x_5241_ = l_Lean_Environment_containsOnBranch(v_env_5231_, v_nextEq_5240_);
                if v___x_5241_ == 0 {
                    crate::leanh::lean_dec(v_nextEq_5240_);
                    crate::leanh::lean_dec(v___x_5237_);
                    crate::leanh::lean_dec_ref(v_env_5231_);
                    crate::leanh::lean_dec(v_declName_5230_);
                    v___x_5242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5242_, 0, v_eqs_5233_);
                    return v___x_5242_;
                } else {
                    v___x_5243_ = lean_array_push(v_eqs_5233_, v_nextEq_5240_);
                    v_idx_5232_ = v___x_5237_;
                    v_eqs_5233_ = v___x_5243_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg___boxed(
    mut v_declName_5245_: *mut crate::leanh::LeanObject,
    mut v_env_5246_: *mut crate::leanh::LeanObject,
    mut v_idx_5247_: *mut crate::leanh::LeanObject,
    mut v_eqs_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5250_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(
        v_declName_5245_,
        v_env_5246_,
        v_idx_5247_,
        v_eqs_5248_,
    );
    return v_res_5250_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(
    mut v_declName_5251_: *mut crate::leanh::LeanObject,
    mut v_env_5252_: *mut crate::leanh::LeanObject,
    mut v_idx_5253_: *mut crate::leanh::LeanObject,
    mut v_eqs_5254_: *mut crate::leanh::LeanObject,
    mut v_a_5255_: *mut crate::leanh::LeanObject,
    mut v_a_5256_: *mut crate::leanh::LeanObject,
    mut v_a_5257_: *mut crate::leanh::LeanObject,
    mut v_a_5258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5260_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(
        v_declName_5251_,
        v_env_5252_,
        v_idx_5253_,
        v_eqs_5254_,
    );
    return v___x_5260_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(
    mut v_declName_5261_: *mut crate::leanh::LeanObject,
    mut v_env_5262_: *mut crate::leanh::LeanObject,
    mut v_idx_5263_: *mut crate::leanh::LeanObject,
    mut v_eqs_5264_: *mut crate::leanh::LeanObject,
    mut v_a_5265_: *mut crate::leanh::LeanObject,
    mut v_a_5266_: *mut crate::leanh::LeanObject,
    mut v_a_5267_: *mut crate::leanh::LeanObject,
    mut v_a_5268_: *mut crate::leanh::LeanObject,
    mut v_a_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(
        v_declName_5261_,
        v_env_5262_,
        v_idx_5263_,
        v_eqs_5264_,
        v_a_5265_,
        v_a_5266_,
        v_a_5267_,
        v_a_5268_,
    );
    crate::leanh::lean_dec(v_a_5268_);
    crate::leanh::lean_dec_ref(v_a_5267_);
    crate::leanh::lean_dec(v_a_5266_);
    crate::leanh::lean_dec_ref(v_a_5265_);
    return v_res_5270_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(
    mut v_declName_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v___x_5279_: u8 = 0;
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_unused_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5274_ = lean_st_ref_get(v_a_5272_);
                v_env_5275_ = crate::leanh::lean_ctor_get(v___x_5274_, 0);
                crate::leanh::lean_inc_ref_n(v_env_5275_, 3);
                crate::leanh::lean_dec(v___x_5274_);
                v___x_5276_ = l_Lean_Meta_eqn1ThmSuffix___closed__0;
                crate::leanh::lean_inc(v_declName_5271_);
                v___x_5277_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_5275_, v_declName_5271_, v___x_5276_);
                v___x_5278_ = 1;
                crate::leanh::lean_inc(v___x_5277_);
                v___x_5279_ = l_Lean_Environment_contains(v_env_5275_, v___x_5277_, v___x_5278_);
                if v___x_5279_ == 0 {
                    crate::leanh::lean_dec(v___x_5277_);
                    crate::leanh::lean_dec_ref(v_env_5275_);
                    crate::leanh::lean_dec(v_declName_5271_);
                    v___x_5280_ = crate::leanh::lean_box(0);
                    v___x_5281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5281_, 0, v___x_5280_);
                    return v___x_5281_;
                } else {
                    v___x_5282_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5283_ = lean_mk_empty_array_with_capacity(v___x_5282_);
                    v___x_5284_ = lean_array_push(v___x_5283_, v___x_5277_);
                    crate::leanh::lean_inc(v_declName_5271_);
                    v___x_5285_ =
                        l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(
                            v_declName_5271_,
                            v_env_5275_,
                            v___x_5282_,
                            v___x_5284_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5285_) == 0 {
                        v_a_5286_ = crate::leanh::lean_ctor_get(v___x_5285_, 0);
                        crate::leanh::lean_inc_n(v_a_5286_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5285_, 1);
                        v___x_5287_ =
                            l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(
                                v_declName_5271_,
                                v_a_5286_,
                                v_a_5272_,
                            );
                        v_isSharedCheck_5295_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5287_)) as u8;
                        if v_isSharedCheck_5295_ == 0 {
                            v_unused_5296_ = crate::leanh::lean_ctor_get(v___x_5287_, 0);
                            crate::leanh::lean_dec(v_unused_5296_);
                            v___x_5289_ = v___x_5287_;
                            v_isShared_5290_ = v_isSharedCheck_5295_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5287_);
                            v___x_5289_ = crate::leanh::lean_box(0);
                            v_isShared_5290_ = v_isSharedCheck_5295_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5271_);
                        v_a_5297_ = crate::leanh::lean_ctor_get(v___x_5285_, 0);
                        v_isSharedCheck_5304_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5285_)) as u8;
                        if v_isSharedCheck_5304_ == 0 {
                            v___x_5299_ = v___x_5285_;
                            v_isShared_5300_ = v_isSharedCheck_5304_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5297_);
                            crate::leanh::lean_dec(v___x_5285_);
                            v___x_5299_ = crate::leanh::lean_box(0);
                            v_isShared_5300_ = v_isSharedCheck_5304_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5291_, 0, v_a_5286_);
                if v_isShared_5290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5291_);
                    v___x_5293_ = v___x_5289_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5291_);
                    v___x_5293_ = v_reuseFailAlloc_5294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5293_;
            }
            3 => {
                if v_isShared_5300_ == 0 {
                    v___x_5302_ = v___x_5299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
                    v___x_5302_ = v_reuseFailAlloc_5303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(
    mut v_declName_5305_: *mut crate::leanh::LeanObject,
    mut v_a_5306_: *mut crate::leanh::LeanObject,
    mut v_a_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5308_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(
        v_declName_5305_,
        v_a_5306_,
    );
    crate::leanh::lean_dec(v_a_5306_);
    return v_res_5308_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(
    mut v_declName_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_a_5311_: *mut crate::leanh::LeanObject,
    mut v_a_5312_: *mut crate::leanh::LeanObject,
    mut v_a_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5315_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(
        v_declName_5309_,
        v_a_5313_,
    );
    return v___x_5315_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(
    mut v_declName_5316_: *mut crate::leanh::LeanObject,
    mut v_a_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5322_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(
        v_declName_5316_,
        v_a_5317_,
        v_a_5318_,
        v_a_5319_,
        v_a_5320_,
    );
    crate::leanh::lean_dec(v_a_5320_);
    crate::leanh::lean_dec_ref(v_a_5319_);
    crate::leanh::lean_dec(v_a_5318_);
    crate::leanh::lean_dec_ref(v_a_5317_);
    return v_res_5322_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(
    mut v_lctx_5323_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5324_: *mut crate::leanh::LeanObject,
    mut v_x_5325_: *mut crate::leanh::LeanObject,
    mut v___y_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5335_: u8 = 0;
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5339_: u8 = 0;
    let mut v_a_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    crate::leanh::lean_box(0),
                    v_lctx_5323_,
                    v_localInsts_5324_,
                    v_x_5325_,
                    v___y_5326_,
                    v___y_5327_,
                    v___y_5328_,
                    v___y_5329_,
                );
                if crate::leanh::lean_obj_tag(v___x_5331_) == 0 {
                    v_a_5332_ = crate::leanh::lean_ctor_get(v___x_5331_, 0);
                    v_isSharedCheck_5339_ = (!crate::leanh::lean_is_exclusive(v___x_5331_)) as u8;
                    if v_isSharedCheck_5339_ == 0 {
                        v___x_5334_ = v___x_5331_;
                        v_isShared_5335_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5332_);
                        crate::leanh::lean_dec(v___x_5331_);
                        v___x_5334_ = crate::leanh::lean_box(0);
                        v_isShared_5335_ = v_isSharedCheck_5339_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5340_ = crate::leanh::lean_ctor_get(v___x_5331_, 0);
                    v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v___x_5331_)) as u8;
                    if v_isSharedCheck_5347_ == 0 {
                        v___x_5342_ = v___x_5331_;
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5340_);
                        crate::leanh::lean_dec(v___x_5331_);
                        v___x_5342_ = crate::leanh::lean_box(0);
                        v_isShared_5343_ = v_isSharedCheck_5347_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5335_ == 0 {
                    v___x_5337_ = v___x_5334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
                    v___x_5337_ = v_reuseFailAlloc_5338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5337_;
            }
            3 => {
                if v_isShared_5343_ == 0 {
                    v___x_5345_ = v___x_5342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg___boxed(
    mut v_lctx_5348_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5349_: *mut crate::leanh::LeanObject,
    mut v_x_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5356_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_5348_, v_localInsts_5349_, v_x_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
    crate::leanh::lean_dec(v___y_5354_);
    crate::leanh::lean_dec_ref(v___y_5353_);
    crate::leanh::lean_dec(v___y_5352_);
    crate::leanh::lean_dec_ref(v___y_5351_);
    return v_res_5356_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(
    mut v_00_u03b1_5357_: *mut crate::leanh::LeanObject,
    mut v_lctx_5358_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5359_: *mut crate::leanh::LeanObject,
    mut v_x_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5366_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v_lctx_5358_, v_localInsts_5359_, v_x_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
    return v___x_5366_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___boxed(
    mut v_00_u03b1_5367_: *mut crate::leanh::LeanObject,
    mut v_lctx_5368_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5369_: *mut crate::leanh::LeanObject,
    mut v_x_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5376_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1(v_00_u03b1_5367_, v_lctx_5368_, v_localInsts_5369_, v_x_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_);
    crate::leanh::lean_dec(v___y_5374_);
    crate::leanh::lean_dec_ref(v___y_5373_);
    crate::leanh::lean_dec(v___y_5372_);
    crate::leanh::lean_dec_ref(v___y_5371_);
    return v_res_5376_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(
    mut v_declName_5380_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5381_: *mut crate::leanh::LeanObject,
    mut v_b_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5398_: u8 = 0;
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v_unused_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5381_) == 0 {
                    crate::leanh::lean_dec(v_declName_5380_);
                    v___x_5388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5388_, 0, v_b_5382_);
                    return v___x_5388_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5382_);
                    v_head_5389_ = crate::leanh::lean_ctor_get(v_as_x27_5381_, 0);
                    v_tail_5390_ = crate::leanh::lean_ctor_get(v_as_x27_5381_, 1);
                    crate::leanh::lean_inc(v_head_5389_);
                    crate::leanh::lean_inc(v___y_5386_);
                    crate::leanh::lean_inc_ref(v___y_5385_);
                    crate::leanh::lean_inc(v___y_5384_);
                    crate::leanh::lean_inc_ref(v___y_5383_);
                    crate::leanh::lean_inc(v_declName_5380_);
                    v___x_5391_ = crate::leanh::lean_apply_6(
                        v_head_5389_,
                        v_declName_5380_,
                        v___y_5383_,
                        v___y_5384_,
                        v___y_5385_,
                        v___y_5386_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5391_) == 0 {
                        v_a_5392_ = crate::leanh::lean_ctor_get(v___x_5391_, 0);
                        crate::leanh::lean_inc(v_a_5392_);
                        crate::leanh::lean_dec_ref_known(v___x_5391_, 1);
                        v___x_5393_ = crate::leanh::lean_box(0);
                        if crate::leanh::lean_obj_tag(v_a_5392_) == 1 {
                            v_val_5394_ = crate::leanh::lean_ctor_get(v_a_5392_, 0);
                            crate::leanh::lean_inc(v_val_5394_);
                            v___x_5395_ =
                                l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(
                                    v_declName_5380_,
                                    v_val_5394_,
                                    v___y_5386_,
                                );
                            v_isSharedCheck_5404_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5395_)) as u8;
                            if v_isSharedCheck_5404_ == 0 {
                                v_unused_5405_ = crate::leanh::lean_ctor_get(v___x_5395_, 0);
                                crate::leanh::lean_dec(v_unused_5405_);
                                v___x_5397_ = v___x_5395_;
                                v_isShared_5398_ = v_isSharedCheck_5404_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5395_);
                                v___x_5397_ = crate::leanh::lean_box(0);
                                v_isShared_5398_ = v_isSharedCheck_5404_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5392_);
                            v___x_5406_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0;
                            v_as_x27_5381_ = v_tail_5390_;
                            v_b_5382_ = v___x_5406_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5380_);
                        v_a_5408_ = crate::leanh::lean_ctor_get(v___x_5391_, 0);
                        v_isSharedCheck_5415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5391_)) as u8;
                        if v_isSharedCheck_5415_ == 0 {
                            v___x_5410_ = v___x_5391_;
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5408_);
                            crate::leanh::lean_dec(v___x_5391_);
                            v___x_5410_ = crate::leanh::lean_box(0);
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5399_, 0, v_a_5392_);
                v___x_5400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5399_);
                crate::leanh::lean_ctor_set(v___x_5400_, 1, v___x_5393_);
                if v_isShared_5398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5397_, 0, v___x_5400_);
                    v___x_5402_ = v___x_5397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5400_);
                    v___x_5402_ = v_reuseFailAlloc_5403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5402_;
            }
            3 => {
                if v_isShared_5411_ == 0 {
                    v___x_5413_ = v___x_5410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
                    v___x_5413_ = v_reuseFailAlloc_5414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___boxed(
    mut v_declName_5416_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5417_: *mut crate::leanh::LeanObject,
    mut v_b_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5424_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_5416_, v_as_x27_5417_, v_b_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
    crate::leanh::lean_dec(v___y_5422_);
    crate::leanh::lean_dec_ref(v___y_5421_);
    crate::leanh::lean_dec(v___y_5420_);
    crate::leanh::lean_dec_ref(v___y_5419_);
    crate::leanh::lean_dec(v_as_x27_5417_);
    return v_res_5424_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(
    mut v_declName_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v___x_5436_: u8 = 0;
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v_fst_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut v_a_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_a_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5473_: u8 = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_5425_);
                v___x_5431_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(
                    v_declName_5425_,
                    v___y_5426_,
                    v___y_5427_,
                    v___y_5428_,
                    v___y_5429_,
                );
                if crate::leanh::lean_obj_tag(v___x_5431_) == 0 {
                    v_a_5432_ = crate::leanh::lean_ctor_get(v___x_5431_, 0);
                    v_isSharedCheck_5469_ = (!crate::leanh::lean_is_exclusive(v___x_5431_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v___x_5434_ = v___x_5431_;
                        v_isShared_5435_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5432_);
                        crate::leanh::lean_dec(v___x_5431_);
                        v___x_5434_ = crate::leanh::lean_box(0);
                        v_isShared_5435_ = v_isSharedCheck_5469_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5425_);
                    v_a_5470_ = crate::leanh::lean_ctor_get(v___x_5431_, 0);
                    v_isSharedCheck_5477_ = (!crate::leanh::lean_is_exclusive(v___x_5431_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v___x_5472_ = v___x_5431_;
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5470_);
                        crate::leanh::lean_dec(v___x_5431_);
                        v___x_5472_ = crate::leanh::lean_box(0);
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5436_ = (crate::leanh::lean_unbox(v_a_5432_) as u8);
                crate::leanh::lean_dec(v_a_5432_);
                if v___x_5436_ == 0 {
                    crate::leanh::lean_dec(v_declName_5425_);
                    v___x_5437_ = crate::leanh::lean_box(0);
                    if v_isShared_5435_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5434_, 0, v___x_5437_);
                        v___x_5439_ = v___x_5434_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5437_);
                        v___x_5439_ = v_reuseFailAlloc_5440_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5434_);
                    crate::leanh::lean_inc(v_declName_5425_);
                    v___x_5441_ =
                        l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(
                            v_declName_5425_,
                            v___y_5429_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5441_) == 0 {
                        v_a_5442_ = crate::leanh::lean_ctor_get(v___x_5441_, 0);
                        crate::leanh::lean_inc(v_a_5442_);
                        if crate::leanh::lean_obj_tag(v_a_5442_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_a_5442_, 1);
                            crate::leanh::lean_dec(v_declName_5425_);
                            return v___x_5441_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_5441_, 1);
                            crate::leanh::lean_dec(v_a_5442_);
                            v___x_5443_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
                            v___x_5444_ = lean_st_ref_get(v___x_5443_);
                            v___x_5445_ = crate::leanh::lean_box(0);
                            v___x_5446_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg___closed__0;
                            v___x_5447_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_5425_, v___x_5444_, v___x_5446_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
                            crate::leanh::lean_dec(v___x_5444_);
                            if crate::leanh::lean_obj_tag(v___x_5447_) == 0 {
                                v_a_5448_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                                v_isSharedCheck_5460_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5447_)) as u8;
                                if v_isSharedCheck_5460_ == 0 {
                                    v___x_5450_ = v___x_5447_;
                                    v_isShared_5451_ = v_isSharedCheck_5460_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5448_);
                                    crate::leanh::lean_dec(v___x_5447_);
                                    v___x_5450_ = crate::leanh::lean_box(0);
                                    v_isShared_5451_ = v_isSharedCheck_5460_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_5461_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                                v_isSharedCheck_5468_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5447_)) as u8;
                                if v_isSharedCheck_5468_ == 0 {
                                    v___x_5463_ = v___x_5447_;
                                    v_isShared_5464_ = v_isSharedCheck_5468_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5461_);
                                    crate::leanh::lean_dec(v___x_5447_);
                                    v___x_5463_ = crate::leanh::lean_box(0);
                                    v_isShared_5464_ = v_isSharedCheck_5468_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5425_);
                        return v___x_5441_;
                    }
                }
            }
            2 => {
                return v___x_5439_;
            }
            3 => {
                v_fst_5452_ = crate::leanh::lean_ctor_get(v_a_5448_, 0);
                crate::leanh::lean_inc(v_fst_5452_);
                crate::leanh::lean_dec(v_a_5448_);
                if crate::leanh::lean_obj_tag(v_fst_5452_) == 0 {
                    if v_isShared_5451_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5450_, 0, v___x_5445_);
                        v___x_5454_ = v___x_5450_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 0, v___x_5445_);
                        v___x_5454_ = v_reuseFailAlloc_5455_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_5456_ = crate::leanh::lean_ctor_get(v_fst_5452_, 0);
                    crate::leanh::lean_inc(v_val_5456_);
                    crate::leanh::lean_dec_ref_known(v_fst_5452_, 1);
                    if v_isShared_5451_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5450_, 0, v_val_5456_);
                        v___x_5458_ = v___x_5450_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_val_5456_);
                        v___x_5458_ = v_reuseFailAlloc_5459_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5454_;
            }
            5 => {
                return v___x_5458_;
            }
            6 => {
                if v_isShared_5464_ == 0 {
                    v___x_5466_ = v___x_5463_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
                    v___x_5466_ = v_reuseFailAlloc_5467_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5466_;
            }
            8 => {
                if v_isShared_5473_ == 0 {
                    v___x_5475_ = v___x_5472_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
                    v___x_5475_ = v_reuseFailAlloc_5476_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed(
    mut v_declName_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5484_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(
        v_declName_5478_,
        v___y_5479_,
        v___y_5480_,
        v___y_5481_,
        v___y_5482_,
    );
    crate::leanh::lean_dec(v___y_5482_);
    crate::leanh::lean_dec_ref(v___y_5481_);
    crate::leanh::lean_dec(v___y_5480_);
    crate::leanh::lean_dec_ref(v___y_5479_);
    return v_res_5484_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5485_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5485_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5486_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0,
    );
    v___x_5487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5487_, 0, v___x_5486_);
    return v___x_5487_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5488_ = crate::leanh::lean_box(1);
    v___x_5489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
    v___x_5490_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1,
    );
    v___x_5491_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5491_, 0, v___x_5490_);
    crate::leanh::lean_ctor_set(v___x_5491_, 1, v___x_5489_);
    crate::leanh::lean_ctor_set(v___x_5491_, 2, v___x_5488_);
    return v___x_5491_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(
    mut v_declName_5494_: *mut crate::leanh::LeanObject,
    mut v_a_5495_: *mut crate::leanh::LeanObject,
    mut v_a_5496_: *mut crate::leanh::LeanObject,
    mut v_a_5497_: *mut crate::leanh::LeanObject,
    mut v_a_5498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5500_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5500_, 0, v_declName_5494_);
    v___x_5501_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2,
    );
    v___x_5502_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
    v___x_5503_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_5501_, v___x_5502_, v___f_5500_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_);
    return v___x_5503_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed(
    mut v_declName_5504_: *mut crate::leanh::LeanObject,
    mut v_a_5505_: *mut crate::leanh::LeanObject,
    mut v_a_5506_: *mut crate::leanh::LeanObject,
    mut v_a_5507_: *mut crate::leanh::LeanObject,
    mut v_a_5508_: *mut crate::leanh::LeanObject,
    mut v_a_5509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5510_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(
        v_declName_5504_,
        v_a_5505_,
        v_a_5506_,
        v_a_5507_,
        v_a_5508_,
    );
    crate::leanh::lean_dec(v_a_5508_);
    crate::leanh::lean_dec_ref(v_a_5507_);
    crate::leanh::lean_dec(v_a_5506_);
    crate::leanh::lean_dec_ref(v_a_5505_);
    return v_res_5510_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(
    mut v_declName_5511_: *mut crate::leanh::LeanObject,
    mut v_as_5512_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5513_: *mut crate::leanh::LeanObject,
    mut v_b_5514_: *mut crate::leanh::LeanObject,
    mut v_a_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(v_declName_5511_, v_as_x27_5513_, v_b_5514_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_);
    return v___x_5521_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(
    mut v_declName_5522_: *mut crate::leanh::LeanObject,
    mut v_as_5523_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5524_: *mut crate::leanh::LeanObject,
    mut v_b_5525_: *mut crate::leanh::LeanObject,
    mut v_a_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
    mut v___y_5529_: *mut crate::leanh::LeanObject,
    mut v___y_5530_: *mut crate::leanh::LeanObject,
    mut v___y_5531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(v_declName_5522_, v_as_5523_, v_as_x27_5524_, v_b_5525_, v_a_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
    crate::leanh::lean_dec(v___y_5530_);
    crate::leanh::lean_dec_ref(v___y_5529_);
    crate::leanh::lean_dec(v___y_5528_);
    crate::leanh::lean_dec_ref(v___y_5527_);
    crate::leanh::lean_dec(v_as_x27_5524_);
    crate::leanh::lean_dec(v_as_5523_);
    return v_res_5532_;
}
pub unsafe fn l_Lean_Meta_getEqnsFor_x3f(
    mut v_declName_5533_: *mut crate::leanh::LeanObject,
    mut v_a_5534_: *mut crate::leanh::LeanObject,
    mut v_a_5535_: *mut crate::leanh::LeanObject,
    mut v_a_5536_: *mut crate::leanh::LeanObject,
    mut v_a_5537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5540_ = lean_mk_empty_array_with_capacity(v___x_5539_);
    crate::leanh::lean_dec_ref(v___x_5540_);
    v___x_5541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2,
    );
    v___x_5542_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
    crate::leanh::lean_inc(v_declName_5533_);
    v___x_5543_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_5543_, 0, v_declName_5533_);
    v___x_5544_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_withEqnOptions___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_5544_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_5544_, 1, v_declName_5533_);
    crate::leanh::lean_closure_set(v___x_5544_, 2, v___x_5543_);
    v___x_5545_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_5541_, v___x_5542_, v___x_5544_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_);
    return v___x_5545_;
}
pub unsafe fn l_Lean_Meta_getEqnsFor_x3f___boxed(
    mut v_declName_5546_: *mut crate::leanh::LeanObject,
    mut v_a_5547_: *mut crate::leanh::LeanObject,
    mut v_a_5548_: *mut crate::leanh::LeanObject,
    mut v_a_5549_: *mut crate::leanh::LeanObject,
    mut v_a_5550_: *mut crate::leanh::LeanObject,
    mut v_a_5551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5552_ =
        l_Lean_Meta_getEqnsFor_x3f(v_declName_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_);
    crate::leanh::lean_dec(v_a_5550_);
    crate::leanh::lean_dec_ref(v_a_5549_);
    crate::leanh::lean_dec(v_a_5548_);
    crate::leanh::lean_dec_ref(v_a_5547_);
    return v_res_5552_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(
    mut v_msgData_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5559_ = lean_st_ref_get(v___y_5557_);
    v_env_5560_ = crate::leanh::lean_ctor_get(v___x_5559_, 0);
    crate::leanh::lean_inc_ref(v_env_5560_);
    crate::leanh::lean_dec(v___x_5559_);
    v___x_5561_ = lean_st_ref_get(v___y_5555_);
    v_mctx_5562_ = crate::leanh::lean_ctor_get(v___x_5561_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5562_);
    crate::leanh::lean_dec(v___x_5561_);
    v_lctx_5563_ = crate::leanh::lean_ctor_get(v___y_5554_, 2);
    v_options_5564_ = crate::leanh::lean_ctor_get(v___y_5556_, 2);
    crate::leanh::lean_inc_ref(v_options_5564_);
    crate::leanh::lean_inc_ref(v_lctx_5563_);
    v___x_5565_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5565_, 0, v_env_5560_);
    crate::leanh::lean_ctor_set(v___x_5565_, 1, v_mctx_5562_);
    crate::leanh::lean_ctor_set(v___x_5565_, 2, v_lctx_5563_);
    crate::leanh::lean_ctor_set(v___x_5565_, 3, v_options_5564_);
    v___x_5566_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5566_, 0, v___x_5565_);
    crate::leanh::lean_ctor_set(v___x_5566_, 1, v_msgData_5553_);
    v___x_5567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5567_, 0, v___x_5566_);
    return v___x_5567_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1___boxed(
    mut v_msgData_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5574_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msgData_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
    crate::leanh::lean_dec(v___y_5572_);
    crate::leanh::lean_dec_ref(v___y_5571_);
    crate::leanh::lean_dec(v___y_5570_);
    crate::leanh::lean_dec_ref(v___y_5569_);
    return v_res_5574_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0()
-> f64 {
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: f64 = 0.0;
    v___x_5575_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5576_ = lean_float_of_nat(v___x_5575_);
    return v___x_5576_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(
    mut v_cls_5580_: *mut crate::leanh::LeanObject,
    mut v_msg_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5592_: u8 = 0;
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5605_: u8 = 0;
    let mut v_tid_5606_: u64 = 0;
    let mut v_traces_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5610_: u8 = 0;
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: f64 = 0.0;
    let mut v___x_5613_: u8 = 0;
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5631_: u8 = 0;
    let mut v_isSharedCheck_5632_: u8 = 0;
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5587_ = crate::leanh::lean_ctor_get(v___y_5584_, 5);
                v___x_5588_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
                v_a_5589_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                v_isSharedCheck_5633_ = (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                if v_isSharedCheck_5633_ == 0 {
                    v___x_5591_ = v___x_5588_;
                    v_isShared_5592_ = v_isSharedCheck_5633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5589_);
                    crate::leanh::lean_dec(v___x_5588_);
                    v___x_5591_ = crate::leanh::lean_box(0);
                    v_isShared_5592_ = v_isSharedCheck_5633_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5593_ = lean_st_ref_take(v___y_5585_);
                v_traceState_5594_ = crate::leanh::lean_ctor_get(v___x_5593_, 4);
                v_env_5595_ = crate::leanh::lean_ctor_get(v___x_5593_, 0);
                v_nextMacroScope_5596_ = crate::leanh::lean_ctor_get(v___x_5593_, 1);
                v_ngen_5597_ = crate::leanh::lean_ctor_get(v___x_5593_, 2);
                v_auxDeclNGen_5598_ = crate::leanh::lean_ctor_get(v___x_5593_, 3);
                v_cache_5599_ = crate::leanh::lean_ctor_get(v___x_5593_, 5);
                v_messages_5600_ = crate::leanh::lean_ctor_get(v___x_5593_, 6);
                v_infoState_5601_ = crate::leanh::lean_ctor_get(v___x_5593_, 7);
                v_snapshotTasks_5602_ = crate::leanh::lean_ctor_get(v___x_5593_, 8);
                v_isSharedCheck_5632_ = (!crate::leanh::lean_is_exclusive(v___x_5593_)) as u8;
                if v_isSharedCheck_5632_ == 0 {
                    v___x_5604_ = v___x_5593_;
                    v_isShared_5605_ = v_isSharedCheck_5632_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5602_);
                    crate::leanh::lean_inc(v_infoState_5601_);
                    crate::leanh::lean_inc(v_messages_5600_);
                    crate::leanh::lean_inc(v_cache_5599_);
                    crate::leanh::lean_inc(v_traceState_5594_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5598_);
                    crate::leanh::lean_inc(v_ngen_5597_);
                    crate::leanh::lean_inc(v_nextMacroScope_5596_);
                    crate::leanh::lean_inc(v_env_5595_);
                    crate::leanh::lean_dec(v___x_5593_);
                    v___x_5604_ = crate::leanh::lean_box(0);
                    v_isShared_5605_ = v_isSharedCheck_5632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_5606_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_5594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_5607_ = crate::leanh::lean_ctor_get(v_traceState_5594_, 0);
                v_isSharedCheck_5631_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_5594_)) as u8;
                if v_isSharedCheck_5631_ == 0 {
                    v___x_5609_ = v_traceState_5594_;
                    v_isShared_5610_ = v_isSharedCheck_5631_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_5607_);
                    crate::leanh::lean_dec(v_traceState_5594_);
                    v___x_5609_ = crate::leanh::lean_box(0);
                    v_isShared_5610_ = v_isSharedCheck_5631_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5611_ = crate::leanh::lean_box(0);
                v___x_5612_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
                v___x_5613_ = 0;
                v___x_5614_ =
                    l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1;
                v___x_5615_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_5615_, 0, v_cls_5580_);
                crate::leanh::lean_ctor_set(v___x_5615_, 1, v___x_5611_);
                crate::leanh::lean_ctor_set(v___x_5615_, 2, v___x_5614_);
                crate::leanh::lean_ctor_set_float(
                    v___x_5615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5612_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_5615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_5612_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_5613_,
                );
                v___x_5616_ =
                    l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__2;
                v___x_5617_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5617_, 0, v___x_5615_);
                crate::leanh::lean_ctor_set(v___x_5617_, 1, v_a_5589_);
                crate::leanh::lean_ctor_set(v___x_5617_, 2, v___x_5616_);
                crate::leanh::lean_inc(v_ref_5587_);
                v___x_5618_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5618_, 0, v_ref_5587_);
                crate::leanh::lean_ctor_set(v___x_5618_, 1, v___x_5617_);
                v___x_5619_ = l_Lean_PersistentArray_push___redArg(v_traces_5607_, v___x_5618_);
                if v_isShared_5610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5609_, 0, v___x_5619_);
                    v___x_5621_ = v___x_5609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5630_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5619_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_5630_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_5606_,
                    );
                    v___x_5621_ = v_reuseFailAlloc_5630_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5604_, 4, v___x_5621_);
                    v___x_5623_ = v___x_5604_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_env_5595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 1, v_nextMacroScope_5596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_ngen_5597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 3, v_auxDeclNGen_5598_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 4, v___x_5621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 5, v_cache_5599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 6, v_messages_5600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 7, v_infoState_5601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 8, v_snapshotTasks_5602_);
                    v___x_5623_ = v_reuseFailAlloc_5629_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5624_ = lean_st_ref_set(v___y_5585_, v___x_5623_);
                v___x_5625_ = crate::leanh::lean_box(0);
                if v_isShared_5592_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5591_, 0, v___x_5625_);
                    v___x_5627_ = v___x_5591_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5628_, 0, v___x_5625_);
                    v___x_5627_ = v_reuseFailAlloc_5628_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5627_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___boxed(
    mut v_cls_5634_: *mut crate::leanh::LeanObject,
    mut v_msg_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5641_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(
        v_cls_5634_,
        v_msg_5635_,
        v___y_5636_,
        v___y_5637_,
        v___y_5638_,
        v___y_5639_,
    );
    crate::leanh::lean_dec(v___y_5639_);
    crate::leanh::lean_dec_ref(v___y_5638_);
    crate::leanh::lean_dec(v___y_5637_);
    crate::leanh::lean_dec_ref(v___y_5636_);
    return v_res_5641_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(
    mut v___x_5642_: *mut crate::leanh::LeanObject,
    mut v_as_5643_: *mut crate::leanh::LeanObject,
    mut v_sz_5644_: usize,
    mut v_i_5645_: usize,
    mut v_b_5646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: usize = 0;
    let mut v___x_5651_: usize = 0;
    let mut v___x_5653_: u8 = 0;
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: u8 = 0;
    let mut v___y_5659_: u8 = 0;
    let mut v_name_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5669_: u8 = 0;
    let mut v_unused_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: u8 = 0;
    let mut v___x_5672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5653_ = lean_usize_dec_lt(v_i_5645_, v_sz_5644_);
                if v___x_5653_ == 0 {
                    v___x_5654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5654_, 0, v_b_5646_);
                    return v___x_5654_;
                } else {
                    v_a_5655_ = lean_array_uget(v_as_5643_, v_i_5645_);
                    v_defValue_5656_ = crate::leanh::lean_ctor_get(v_a_5655_, 1);
                    v___x_5657_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                        v___x_5642_,
                        v_a_5655_,
                    );
                    if v___x_5657_ == 0 {
                        v___x_5671_ = (crate::leanh::lean_unbox(v_defValue_5656_) as u8);
                        if v___x_5671_ == 0 {
                            v___y_5659_ = v___x_5653_;
                            state = 2;
                            continue;
                        } else {
                            v___y_5659_ = v___x_5657_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_5672_ = (crate::leanh::lean_unbox(v_defValue_5656_) as u8);
                        v___y_5659_ = v___x_5672_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5650_ = 1usize;
                v___x_5651_ = lean_usize_add(v_i_5645_, v___x_5650_);
                v_i_5645_ = v___x_5651_;
                v_b_5646_ = v_a_5649_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_5659_ == 0 {
                    v_name_5660_ = crate::leanh::lean_ctor_get(v_a_5655_, 0);
                    v_isSharedCheck_5669_ = (!crate::leanh::lean_is_exclusive(v_a_5655_)) as u8;
                    if v_isSharedCheck_5669_ == 0 {
                        v_unused_5670_ = crate::leanh::lean_ctor_get(v_a_5655_, 1);
                        crate::leanh::lean_dec(v_unused_5670_);
                        v___x_5662_ = v_a_5655_;
                        v_isShared_5663_ = v_isSharedCheck_5669_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_name_5660_);
                        crate::leanh::lean_dec(v_a_5655_);
                        v___x_5662_ = crate::leanh::lean_box(0);
                        v_isShared_5663_ = v_isSharedCheck_5669_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5655_);
                    v_a_5649_ = v_b_5646_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5664_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_5664_, 0 as u32, v___x_5657_);
                if v_isShared_5663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5662_, 1, v___x_5664_);
                    v___x_5666_ = v___x_5662_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_name_5660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5668_, 1, v___x_5664_);
                    v___x_5666_ = v_reuseFailAlloc_5668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5667_ = lean_array_push(v_b_5646_, v___x_5666_);
                v_a_5649_ = v___x_5667_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg___boxed(
    mut v___x_5673_: *mut crate::leanh::LeanObject,
    mut v_as_5674_: *mut crate::leanh::LeanObject,
    mut v_sz_5675_: *mut crate::leanh::LeanObject,
    mut v_i_5676_: *mut crate::leanh::LeanObject,
    mut v_b_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5679_: usize = 0;
    let mut v_i_boxed_5680_: usize = 0;
    let mut v_res_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5679_ = crate::leanh::lean_unbox_usize(v_sz_5675_);
    crate::leanh::lean_dec(v_sz_5675_);
    v_i_boxed_5680_ = crate::leanh::lean_unbox_usize(v_i_5676_);
    crate::leanh::lean_dec(v_i_5676_);
    v_res_5681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_5673_, v_as_5674_, v_sz_boxed_5679_, v_i_boxed_5680_, v_b_5677_);
    crate::leanh::lean_dec_ref(v_as_5674_);
    crate::leanh::lean_dec_ref(v___x_5673_);
    return v_res_5681_;
}
pub unsafe fn _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1() -> usize {
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5685_: usize = 0;
    v___x_5684_ = l_Lean_Meta_eqnAffectingOptions;
    v_sz_5685_ = lean_array_size(v___x_5684_);
    return v_sz_5685_;
}
pub unsafe fn _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__1_once),
        _init_l_Lean_Meta_withEqnOptions___redArg___closed__1,
    );
    v___x_5687_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5687_, 0, v___x_5686_);
    crate::leanh::lean_ctor_set(v___x_5687_, 1, v___x_5686_);
    crate::leanh::lean_ctor_set(v___x_5687_, 2, v___x_5686_);
    crate::leanh::lean_ctor_set(v___x_5687_, 3, v___x_5686_);
    crate::leanh::lean_ctor_set(v___x_5687_, 4, v___x_5686_);
    crate::leanh::lean_ctor_set(v___x_5687_, 5, v___x_5686_);
    return v___x_5687_;
}
pub unsafe fn _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5694_ = l_Lean_Meta_saveEqnAffectingOptions___closed__5;
    v___x_5695_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1;
    v___x_5696_ = l_Lean_Name_append(v___x_5695_, v___x_5694_);
    return v___x_5696_;
}
pub unsafe fn _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5698_ = l_Lean_Meta_saveEqnAffectingOptions___closed__7;
    v___x_5699_ = l_Lean_stringToMessageData(v___x_5698_);
    return v___x_5699_;
}
pub unsafe fn l_Lean_Meta_saveEqnAffectingOptions(
    mut v_declName_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
    mut v_a_5704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5711_: usize = 0;
    let mut v___x_5712_: usize = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5717_: u8 = 0;
    let mut v___y_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5756_: u8 = 0;
    let mut v_unused_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5759_: u8 = 0;
    let mut v_unused_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: u8 = 0;
    let mut v_hasTrace_5763_: u8 = 0;
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: u8 = 0;
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v_a_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5777_: u8 = 0;
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5706_ = crate::leanh::lean_ctor_get(v_a_5703_, 2);
                v_inheritedTraceOptions_5707_ = crate::leanh::lean_ctor_get(v_a_5703_, 13);
                v___x_5708_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5709_ = l_Lean_Meta_saveEqnAffectingOptions___closed__0;
                v___x_5710_ = l_Lean_Meta_eqnAffectingOptions;
                v_sz_5711_ = crate::leanh::lean_usize_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__1_once),
                    _init_l_Lean_Meta_saveEqnAffectingOptions___closed__1,
                );
                v___x_5712_ = 0usize;
                v___x_5713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v_options_5706_, v___x_5710_, v_sz_5711_, v___x_5712_, v___x_5709_);
                if crate::leanh::lean_obj_tag(v___x_5713_) == 0 {
                    v_a_5714_ = crate::leanh::lean_ctor_get(v___x_5713_, 0);
                    v_isSharedCheck_5773_ = (!crate::leanh::lean_is_exclusive(v___x_5713_)) as u8;
                    if v_isSharedCheck_5773_ == 0 {
                        v___x_5716_ = v___x_5713_;
                        v_isShared_5717_ = v_isSharedCheck_5773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5714_);
                        crate::leanh::lean_dec(v___x_5713_);
                        v___x_5716_ = crate::leanh::lean_box(0);
                        v_isShared_5717_ = v_isSharedCheck_5773_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_5700_);
                    v_a_5774_ = crate::leanh::lean_ctor_get(v___x_5713_, 0);
                    v_isSharedCheck_5781_ = (!crate::leanh::lean_is_exclusive(v___x_5713_)) as u8;
                    if v_isSharedCheck_5781_ == 0 {
                        v___x_5776_ = v___x_5713_;
                        v_isShared_5777_ = v_isSharedCheck_5781_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5774_);
                        crate::leanh::lean_dec(v___x_5713_);
                        v___x_5776_ = crate::leanh::lean_box(0);
                        v_isShared_5777_ = v_isSharedCheck_5781_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5761_ = lean_array_get_size(v_a_5714_);
                v___x_5762_ = lean_nat_dec_eq(v___x_5761_, v___x_5708_);
                if v___x_5762_ == 0 {
                    v_hasTrace_5763_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5706_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5763_ == 0 {
                        v___y_5719_ = v_a_5702_;
                        v___y_5720_ = v_a_5704_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5764_ = l_Lean_Meta_saveEqnAffectingOptions___closed__5;
                        v___x_5765_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_saveEqnAffectingOptions___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_saveEqnAffectingOptions___closed__6_once
                            ),
                            _init_l_Lean_Meta_saveEqnAffectingOptions___closed__6,
                        );
                        v___x_5766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5707_,
                            v_options_5706_,
                            v___x_5765_,
                        );
                        if v___x_5766_ == 0 {
                            v___y_5719_ = v_a_5702_;
                            v___y_5720_ = v_a_5704_;
                            state = 2;
                            continue;
                        } else {
                            v___x_5767_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_saveEqnAffectingOptions___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_saveEqnAffectingOptions___closed__8_once
                                ),
                                _init_l_Lean_Meta_saveEqnAffectingOptions___closed__8,
                            );
                            crate::leanh::lean_inc(v_declName_5700_);
                            v___x_5768_ = l_Lean_MessageData_ofName(v_declName_5700_);
                            v___x_5769_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5769_, 0, v___x_5767_);
                            crate::leanh::lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                            v___x_5770_ =
                                l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1(
                                    v___x_5764_,
                                    v___x_5769_,
                                    v_a_5701_,
                                    v_a_5702_,
                                    v_a_5703_,
                                    v_a_5704_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_5770_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5770_, 1);
                                v___y_5719_ = v_a_5702_;
                                v___y_5720_ = v_a_5704_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_5716_);
                                crate::leanh::lean_dec(v_a_5714_);
                                crate::leanh::lean_dec(v_declName_5700_);
                                return v___x_5770_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5716_);
                    crate::leanh::lean_dec(v_a_5714_);
                    crate::leanh::lean_dec(v_declName_5700_);
                    v___x_5771_ = crate::leanh::lean_box(0);
                    v___x_5772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5772_, 0, v___x_5771_);
                    return v___x_5772_;
                }
            }
            2 => {
                v___x_5721_ = lean_st_ref_take(v___y_5720_);
                v_env_5722_ = crate::leanh::lean_ctor_get(v___x_5721_, 0);
                v_nextMacroScope_5723_ = crate::leanh::lean_ctor_get(v___x_5721_, 1);
                v_ngen_5724_ = crate::leanh::lean_ctor_get(v___x_5721_, 2);
                v_auxDeclNGen_5725_ = crate::leanh::lean_ctor_get(v___x_5721_, 3);
                v_traceState_5726_ = crate::leanh::lean_ctor_get(v___x_5721_, 4);
                v_messages_5727_ = crate::leanh::lean_ctor_get(v___x_5721_, 6);
                v_infoState_5728_ = crate::leanh::lean_ctor_get(v___x_5721_, 7);
                v_snapshotTasks_5729_ = crate::leanh::lean_ctor_get(v___x_5721_, 8);
                v_isSharedCheck_5759_ = (!crate::leanh::lean_is_exclusive(v___x_5721_)) as u8;
                if v_isSharedCheck_5759_ == 0 {
                    v_unused_5760_ = crate::leanh::lean_ctor_get(v___x_5721_, 5);
                    crate::leanh::lean_dec(v_unused_5760_);
                    v___x_5731_ = v___x_5721_;
                    v_isShared_5732_ = v_isSharedCheck_5759_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5729_);
                    crate::leanh::lean_inc(v_infoState_5728_);
                    crate::leanh::lean_inc(v_messages_5727_);
                    crate::leanh::lean_inc(v_traceState_5726_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5725_);
                    crate::leanh::lean_inc(v_ngen_5724_);
                    crate::leanh::lean_inc(v_nextMacroScope_5723_);
                    crate::leanh::lean_inc(v_env_5722_);
                    crate::leanh::lean_dec(v___x_5721_);
                    v___x_5731_ = crate::leanh::lean_box(0);
                    v_isShared_5732_ = v_isSharedCheck_5759_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5733_ = l_Lean_Meta_eqnOptionsExt;
                v___x_5734_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_5733_,
                    v_env_5722_,
                    v_declName_5700_,
                    v_a_5714_,
                );
                v___x_5735_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2_once),
                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__2,
                );
                if v_isShared_5732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5731_, 5, v___x_5735_);
                    crate::leanh::lean_ctor_set(v___x_5731_, 0, v___x_5734_);
                    v___x_5737_ = v___x_5731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5758_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 0, v___x_5734_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 1, v_nextMacroScope_5723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 2, v_ngen_5724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 3, v_auxDeclNGen_5725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 4, v_traceState_5726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 5, v___x_5735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 6, v_messages_5727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 7, v_infoState_5728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5758_, 8, v_snapshotTasks_5729_);
                    v___x_5737_ = v_reuseFailAlloc_5758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5738_ = lean_st_ref_set(v___y_5720_, v___x_5737_);
                v___x_5739_ = lean_st_ref_take(v___y_5719_);
                v_mctx_5740_ = crate::leanh::lean_ctor_get(v___x_5739_, 0);
                v_zetaDeltaFVarIds_5741_ = crate::leanh::lean_ctor_get(v___x_5739_, 2);
                v_postponed_5742_ = crate::leanh::lean_ctor_get(v___x_5739_, 3);
                v_diag_5743_ = crate::leanh::lean_ctor_get(v___x_5739_, 4);
                v_isSharedCheck_5756_ = (!crate::leanh::lean_is_exclusive(v___x_5739_)) as u8;
                if v_isSharedCheck_5756_ == 0 {
                    v_unused_5757_ = crate::leanh::lean_ctor_get(v___x_5739_, 1);
                    crate::leanh::lean_dec(v_unused_5757_);
                    v___x_5745_ = v___x_5739_;
                    v_isShared_5746_ = v_isSharedCheck_5756_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5743_);
                    crate::leanh::lean_inc(v_postponed_5742_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5741_);
                    crate::leanh::lean_inc(v_mctx_5740_);
                    crate::leanh::lean_dec(v___x_5739_);
                    v___x_5745_ = crate::leanh::lean_box(0);
                    v_isShared_5746_ = v_isSharedCheck_5756_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5747_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__2_once),
                    _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2,
                );
                if v_isShared_5746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5745_, 1, v___x_5747_);
                    v___x_5749_ = v___x_5745_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5755_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_mctx_5740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5747_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5755_,
                        2,
                        v_zetaDeltaFVarIds_5741_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 3, v_postponed_5742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 4, v_diag_5743_);
                    v___x_5749_ = v_reuseFailAlloc_5755_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5750_ = lean_st_ref_set(v___y_5719_, v___x_5749_);
                v___x_5751_ = crate::leanh::lean_box(0);
                if v_isShared_5717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5716_, 0, v___x_5751_);
                    v___x_5753_ = v___x_5716_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5751_);
                    v___x_5753_ = v_reuseFailAlloc_5754_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5753_;
            }
            8 => {
                if v_isShared_5777_ == 0 {
                    v___x_5779_ = v___x_5776_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5774_);
                    v___x_5779_ = v_reuseFailAlloc_5780_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_saveEqnAffectingOptions___boxed(
    mut v_declName_5782_: *mut crate::leanh::LeanObject,
    mut v_a_5783_: *mut crate::leanh::LeanObject,
    mut v_a_5784_: *mut crate::leanh::LeanObject,
    mut v_a_5785_: *mut crate::leanh::LeanObject,
    mut v_a_5786_: *mut crate::leanh::LeanObject,
    mut v_a_5787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5788_ = l_Lean_Meta_saveEqnAffectingOptions(
        v_declName_5782_,
        v_a_5783_,
        v_a_5784_,
        v_a_5785_,
        v_a_5786_,
    );
    crate::leanh::lean_dec(v_a_5786_);
    crate::leanh::lean_dec_ref(v_a_5785_);
    crate::leanh::lean_dec(v_a_5784_);
    crate::leanh::lean_dec_ref(v_a_5783_);
    return v_res_5788_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(
    mut v___x_5789_: *mut crate::leanh::LeanObject,
    mut v_as_5790_: *mut crate::leanh::LeanObject,
    mut v_sz_5791_: usize,
    mut v_i_5792_: usize,
    mut v_b_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___redArg(v___x_5789_, v_as_5790_, v_sz_5791_, v_i_5792_, v_b_5793_);
    return v___x_5799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0___boxed(
    mut v___x_5800_: *mut crate::leanh::LeanObject,
    mut v_as_5801_: *mut crate::leanh::LeanObject,
    mut v_sz_5802_: *mut crate::leanh::LeanObject,
    mut v_i_5803_: *mut crate::leanh::LeanObject,
    mut v_b_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5810_: usize = 0;
    let mut v_i_boxed_5811_: usize = 0;
    let mut v_res_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5810_ = crate::leanh::lean_unbox_usize(v_sz_5802_);
    crate::leanh::lean_dec(v_sz_5802_);
    v_i_boxed_5811_ = crate::leanh::lean_unbox_usize(v_i_5803_);
    crate::leanh::lean_dec(v_i_5803_);
    v_res_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_saveEqnAffectingOptions_spec__0(v___x_5800_, v_as_5801_, v_sz_boxed_5810_, v_i_boxed_5811_, v_b_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
    crate::leanh::lean_dec(v___y_5808_);
    crate::leanh::lean_dec_ref(v___y_5807_);
    crate::leanh::lean_dec(v___y_5806_);
    crate::leanh::lean_dec_ref(v___y_5805_);
    crate::leanh::lean_dec_ref(v_as_5801_);
    crate::leanh::lean_dec_ref(v___x_5800_);
    return v_res_5812_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5814_ = crate::leanh::lean_box(0);
    v___x_5815_ = lean_st_mk_ref(v___x_5814_);
    v___x_5816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5816_, 0, v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2____boxed(
    mut v_a_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5818_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
    return v_res_5818_;
}
pub unsafe fn l_Lean_Meta_registerGetUnfoldEqnFn(
    mut v_f_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5825_: u8 = 0;
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5838_: u8 = 0;
    let mut v_a_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5842_: u8 = 0;
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5821_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_5821_) == 0 {
                    v_a_5822_ = crate::leanh::lean_ctor_get(v___x_5821_, 0);
                    v_isSharedCheck_5838_ = (!crate::leanh::lean_is_exclusive(v___x_5821_)) as u8;
                    if v_isSharedCheck_5838_ == 0 {
                        v___x_5824_ = v___x_5821_;
                        v_isShared_5825_ = v_isSharedCheck_5838_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5822_);
                        crate::leanh::lean_dec(v___x_5821_);
                        v___x_5824_ = crate::leanh::lean_box(0);
                        v_isShared_5825_ = v_isSharedCheck_5838_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5819_);
                    v_a_5839_ = crate::leanh::lean_ctor_get(v___x_5821_, 0);
                    v_isSharedCheck_5846_ = (!crate::leanh::lean_is_exclusive(v___x_5821_)) as u8;
                    if v_isSharedCheck_5846_ == 0 {
                        v___x_5841_ = v___x_5821_;
                        v_isShared_5842_ = v_isSharedCheck_5846_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5839_);
                        crate::leanh::lean_dec(v___x_5821_);
                        v___x_5841_ = crate::leanh::lean_box(0);
                        v_isShared_5842_ = v_isSharedCheck_5846_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5826_ = (crate::leanh::lean_unbox(v_a_5822_) as u8);
                crate::leanh::lean_dec(v_a_5822_);
                if v___x_5826_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_5819_);
                    v___x_5827_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerGetEqnsFn___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerGetEqnsFn___closed__1_once),
                        _init_l_Lean_Meta_registerGetEqnsFn___closed__1,
                    );
                    if v_isShared_5825_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5824_, 1);
                        crate::leanh::lean_ctor_set(v___x_5824_, 0, v___x_5827_);
                        v___x_5829_ = v___x_5824_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5830_, 0, v___x_5827_);
                        v___x_5829_ = v_reuseFailAlloc_5830_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5831_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
                    v___x_5832_ = lean_st_ref_take(v___x_5831_);
                    v___x_5833_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5833_, 0, v_f_5819_);
                    crate::leanh::lean_ctor_set(v___x_5833_, 1, v___x_5832_);
                    v___x_5834_ = lean_st_ref_set(v___x_5831_, v___x_5833_);
                    if v_isShared_5825_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5824_, 0, v___x_5834_);
                        v___x_5836_ = v___x_5824_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5837_, 0, v___x_5834_);
                        v___x_5836_ = v_reuseFailAlloc_5837_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5829_;
            }
            3 => {
                return v___x_5836_;
            }
            4 => {
                if v_isShared_5842_ == 0 {
                    v___x_5844_ = v___x_5841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
                    v___x_5844_ = v_reuseFailAlloc_5845_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_registerGetUnfoldEqnFn___boxed(
    mut v_f_5847_: *mut crate::leanh::LeanObject,
    mut v_a_5848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5849_ = l_Lean_Meta_registerGetUnfoldEqnFn(v_f_5847_);
    return v_res_5849_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(
    mut v_declName_5853_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5854_: *mut crate::leanh::LeanObject,
    mut v_b_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
    mut v___y_5858_: *mut crate::leanh::LeanObject,
    mut v___y_5859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5868_: u8 = 0;
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_a_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5854_) == 0 {
                    crate::leanh::lean_dec(v_declName_5853_);
                    v___x_5861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5861_, 0, v_b_5855_);
                    return v___x_5861_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5855_);
                    v_head_5862_ = crate::leanh::lean_ctor_get(v_as_x27_5854_, 0);
                    v_tail_5863_ = crate::leanh::lean_ctor_get(v_as_x27_5854_, 1);
                    crate::leanh::lean_inc(v_head_5862_);
                    crate::leanh::lean_inc(v___y_5859_);
                    crate::leanh::lean_inc_ref(v___y_5858_);
                    crate::leanh::lean_inc(v___y_5857_);
                    crate::leanh::lean_inc_ref(v___y_5856_);
                    crate::leanh::lean_inc(v_declName_5853_);
                    v___x_5864_ = crate::leanh::lean_apply_6(
                        v_head_5862_,
                        v_declName_5853_,
                        v___y_5856_,
                        v___y_5857_,
                        v___y_5858_,
                        v___y_5859_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5864_) == 0 {
                        v_a_5865_ = crate::leanh::lean_ctor_get(v___x_5864_, 0);
                        v_isSharedCheck_5877_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5864_)) as u8;
                        if v_isSharedCheck_5877_ == 0 {
                            v___x_5867_ = v___x_5864_;
                            v_isShared_5868_ = v_isSharedCheck_5877_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5865_);
                            crate::leanh::lean_dec(v___x_5864_);
                            v___x_5867_ = crate::leanh::lean_box(0);
                            v_isShared_5868_ = v_isSharedCheck_5877_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5853_);
                        v_a_5878_ = crate::leanh::lean_ctor_get(v___x_5864_, 0);
                        v_isSharedCheck_5885_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5864_)) as u8;
                        if v_isSharedCheck_5885_ == 0 {
                            v___x_5880_ = v___x_5864_;
                            v_isShared_5881_ = v_isSharedCheck_5885_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5878_);
                            crate::leanh::lean_dec(v___x_5864_);
                            v___x_5880_ = crate::leanh::lean_box(0);
                            v_isShared_5881_ = v_isSharedCheck_5885_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5869_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_a_5865_) == 1 {
                    crate::leanh::lean_dec(v_declName_5853_);
                    v___x_5870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5870_, 0, v_a_5865_);
                    v___x_5871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5871_, 0, v___x_5870_);
                    crate::leanh::lean_ctor_set(v___x_5871_, 1, v___x_5869_);
                    if v_isShared_5868_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5867_, 0, v___x_5871_);
                        v___x_5873_ = v___x_5867_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5874_, 0, v___x_5871_);
                        v___x_5873_ = v_reuseFailAlloc_5874_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5867_);
                    crate::leanh::lean_dec(v_a_5865_);
                    v___x_5875_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0;
                    v_as_x27_5854_ = v_tail_5863_;
                    v_b_5855_ = v___x_5875_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_5873_;
            }
            3 => {
                if v_isShared_5881_ == 0 {
                    v___x_5883_ = v___x_5880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_a_5878_);
                    v___x_5883_ = v_reuseFailAlloc_5884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___boxed(
    mut v_declName_5886_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5887_: *mut crate::leanh::LeanObject,
    mut v_b_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5894_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(
        v_declName_5886_,
        v_as_x27_5887_,
        v_b_5888_,
        v___y_5889_,
        v___y_5890_,
        v___y_5891_,
        v___y_5892_,
    );
    crate::leanh::lean_dec(v___y_5892_);
    crate::leanh::lean_dec_ref(v___y_5891_);
    crate::leanh::lean_dec(v___y_5890_);
    crate::leanh::lean_dec_ref(v___y_5889_);
    crate::leanh::lean_dec(v_as_x27_5887_);
    return v_res_5894_;
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(
    mut v___x_5895_: *mut crate::leanh::LeanObject,
    mut v_declName_5896_: *mut crate::leanh::LeanObject,
    mut v_nonRec_5897_: u8,
    mut v___x_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: u8 = 0;
    let mut v___x_5910_: u8 = 0;
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: u8 = 0;
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: u8 = 0;
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5928_: u8 = 0;
    let mut v_fst_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5934_: u8 = 0;
    let mut v_a_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5938_: u8 = 0;
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5942_: u8 = 0;
    let mut v_a_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5946_: u8 = 0;
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5950_: u8 = 0;
    let mut v_a_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5954_: u8 = 0;
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5958_: u8 = 0;
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5907_ = lean_st_ref_get(v___y_5902_);
                v_env_5908_ = crate::leanh::lean_ctor_get(v___x_5907_, 0);
                crate::leanh::lean_inc_ref(v_env_5908_);
                crate::leanh::lean_dec(v___x_5907_);
                v___x_5909_ = 1;
                crate::leanh::lean_inc(v___x_5895_);
                v___x_5910_ = l_Lean_Environment_contains(v_env_5908_, v___x_5895_, v___x_5909_);
                if v___x_5910_ == 0 {
                    crate::leanh::lean_dec(v___x_5895_);
                    crate::leanh::lean_inc(v_declName_5896_);
                    v___x_5911_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(
                        v_declName_5896_,
                        v___y_5899_,
                        v___y_5900_,
                        v___y_5901_,
                        v___y_5902_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5911_) == 0 {
                        v_a_5912_ = crate::leanh::lean_ctor_get(v___x_5911_, 0);
                        crate::leanh::lean_inc(v_a_5912_);
                        crate::leanh::lean_dec_ref_known(v___x_5911_, 1);
                        v___x_5913_ = (crate::leanh::lean_unbox(v_a_5912_) as u8);
                        crate::leanh::lean_dec(v_a_5912_);
                        if v___x_5913_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5898_);
                            crate::leanh::lean_dec(v_declName_5896_);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_5896_);
                            v___x_5914_ = l_Lean_Meta_isRecursiveDefinition___redArg(
                                v_declName_5896_,
                                v___y_5902_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5914_) == 0 {
                                v_a_5915_ = crate::leanh::lean_ctor_get(v___x_5914_, 0);
                                crate::leanh::lean_inc(v_a_5915_);
                                crate::leanh::lean_dec_ref_known(v___x_5914_, 1);
                                v___x_5916_ = (crate::leanh::lean_unbox(v_a_5915_) as u8);
                                crate::leanh::lean_dec(v_a_5915_);
                                if v___x_5916_ == 0 {
                                    if v_nonRec_5897_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_5898_);
                                        crate::leanh::lean_dec(v_declName_5896_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5917_ = lean_st_ref_get(v___y_5902_);
                                        v_env_5918_ = crate::leanh::lean_ctor_get(v___x_5917_, 0);
                                        crate::leanh::lean_inc_ref(v_env_5918_);
                                        crate::leanh::lean_dec(v___x_5917_);
                                        crate::leanh::lean_inc(v_declName_5896_);
                                        v___x_5919_ = l_Lean_Meta_mkEqLikeNameFor(
                                            v_env_5918_,
                                            v_declName_5896_,
                                            v___x_5898_,
                                        );
                                        v___x_5920_ = l_Lean_Meta_mkSimpleEqThm(
                                            v_declName_5896_,
                                            v___x_5919_,
                                            v___y_5899_,
                                            v___y_5900_,
                                            v___y_5901_,
                                            v___y_5902_,
                                        );
                                        return v___x_5920_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5898_);
                                    v___x_5921_ =
                                        l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
                                    v___x_5922_ = lean_st_ref_get(v___x_5921_);
                                    v___x_5923_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg___closed__0;
                                    v___x_5924_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(v_declName_5896_, v___x_5922_, v___x_5923_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
                                    crate::leanh::lean_dec(v___x_5922_);
                                    if crate::leanh::lean_obj_tag(v___x_5924_) == 0 {
                                        v_a_5925_ = crate::leanh::lean_ctor_get(v___x_5924_, 0);
                                        v_isSharedCheck_5934_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5924_)) as u8;
                                        if v_isSharedCheck_5934_ == 0 {
                                            v___x_5927_ = v___x_5924_;
                                            v_isShared_5928_ = v_isSharedCheck_5934_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5925_);
                                            crate::leanh::lean_dec(v___x_5924_);
                                            v___x_5927_ = crate::leanh::lean_box(0);
                                            v_isShared_5928_ = v_isSharedCheck_5934_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v_a_5935_ = crate::leanh::lean_ctor_get(v___x_5924_, 0);
                                        v_isSharedCheck_5942_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5924_)) as u8;
                                        if v_isSharedCheck_5942_ == 0 {
                                            v___x_5937_ = v___x_5924_;
                                            v_isShared_5938_ = v_isSharedCheck_5942_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5935_);
                                            crate::leanh::lean_dec(v___x_5924_);
                                            v___x_5937_ = crate::leanh::lean_box(0);
                                            v_isShared_5938_ = v_isSharedCheck_5942_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5898_);
                                crate::leanh::lean_dec(v_declName_5896_);
                                v_a_5943_ = crate::leanh::lean_ctor_get(v___x_5914_, 0);
                                v_isSharedCheck_5950_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5914_)) as u8;
                                if v_isSharedCheck_5950_ == 0 {
                                    v___x_5945_ = v___x_5914_;
                                    v_isShared_5946_ = v_isSharedCheck_5950_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5943_);
                                    crate::leanh::lean_dec(v___x_5914_);
                                    v___x_5945_ = crate::leanh::lean_box(0);
                                    v_isShared_5946_ = v_isSharedCheck_5950_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5898_);
                        crate::leanh::lean_dec(v_declName_5896_);
                        v_a_5951_ = crate::leanh::lean_ctor_get(v___x_5911_, 0);
                        v_isSharedCheck_5958_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5911_)) as u8;
                        if v_isSharedCheck_5958_ == 0 {
                            v___x_5953_ = v___x_5911_;
                            v_isShared_5954_ = v_isSharedCheck_5958_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5951_);
                            crate::leanh::lean_dec(v___x_5911_);
                            v___x_5953_ = crate::leanh::lean_box(0);
                            v_isShared_5954_ = v_isSharedCheck_5958_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5898_);
                    crate::leanh::lean_dec(v_declName_5896_);
                    v___x_5959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5959_, 0, v___x_5895_);
                    v___x_5960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5960_, 0, v___x_5959_);
                    return v___x_5960_;
                }
            }
            1 => {
                v___x_5905_ = crate::leanh::lean_box(0);
                v___x_5906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5906_, 0, v___x_5905_);
                return v___x_5906_;
            }
            2 => {
                v_fst_5929_ = crate::leanh::lean_ctor_get(v_a_5925_, 0);
                crate::leanh::lean_inc(v_fst_5929_);
                crate::leanh::lean_dec(v_a_5925_);
                if crate::leanh::lean_obj_tag(v_fst_5929_) == 0 {
                    crate::leanh::lean_del_object(v___x_5927_);
                    state = 1;
                    continue;
                } else {
                    v_val_5930_ = crate::leanh::lean_ctor_get(v_fst_5929_, 0);
                    crate::leanh::lean_inc(v_val_5930_);
                    crate::leanh::lean_dec_ref_known(v_fst_5929_, 1);
                    if v_isShared_5928_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5927_, 0, v_val_5930_);
                        v___x_5932_ = v___x_5927_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_val_5930_);
                        v___x_5932_ = v_reuseFailAlloc_5933_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5932_;
            }
            4 => {
                if v_isShared_5938_ == 0 {
                    v___x_5940_ = v___x_5937_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_a_5935_);
                    v___x_5940_ = v_reuseFailAlloc_5941_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5940_;
            }
            6 => {
                if v_isShared_5946_ == 0 {
                    v___x_5948_ = v___x_5945_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5949_, 0, v_a_5943_);
                    v___x_5948_ = v_reuseFailAlloc_5949_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5948_;
            }
            8 => {
                if v_isShared_5954_ == 0 {
                    v___x_5956_ = v___x_5953_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_a_5951_);
                    v___x_5956_ = v_reuseFailAlloc_5957_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(
    mut v___x_5961_: *mut crate::leanh::LeanObject,
    mut v_declName_5962_: *mut crate::leanh::LeanObject,
    mut v_nonRec_5963_: *mut crate::leanh::LeanObject,
    mut v___x_5964_: *mut crate::leanh::LeanObject,
    mut v___y_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
    mut v___y_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nonRec_boxed_5970_: u8 = 0;
    let mut v_res_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nonRec_boxed_5970_ = (crate::leanh::lean_unbox(v_nonRec_5963_) as u8);
    v_res_5971_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(
        v___x_5961_,
        v_declName_5962_,
        v_nonRec_boxed_5970_,
        v___x_5964_,
        v___y_5965_,
        v___y_5966_,
        v___y_5967_,
        v___y_5968_,
    );
    crate::leanh::lean_dec(v___y_5968_);
    crate::leanh::lean_dec_ref(v___y_5967_);
    crate::leanh::lean_dec(v___y_5966_);
    crate::leanh::lean_dec_ref(v___y_5965_);
    return v_res_5971_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(
    mut v_msg_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5983_: u8 = 0;
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5978_ = crate::leanh::lean_ctor_get(v___y_5975_, 5);
                v___x_5979_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1_spec__1(v_msg_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_);
                v_a_5980_ = crate::leanh::lean_ctor_get(v___x_5979_, 0);
                v_isSharedCheck_5988_ = (!crate::leanh::lean_is_exclusive(v___x_5979_)) as u8;
                if v_isSharedCheck_5988_ == 0 {
                    v___x_5982_ = v___x_5979_;
                    v_isShared_5983_ = v_isSharedCheck_5988_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5980_);
                    crate::leanh::lean_dec(v___x_5979_);
                    v___x_5982_ = crate::leanh::lean_box(0);
                    v_isShared_5983_ = v_isSharedCheck_5988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5978_);
                v___x_5984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5984_, 0, v_ref_5978_);
                crate::leanh::lean_ctor_set(v___x_5984_, 1, v_a_5980_);
                if v_isShared_5983_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5982_, 1);
                    crate::leanh::lean_ctor_set(v___x_5982_, 0, v___x_5984_);
                    v___x_5986_ = v___x_5982_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v___x_5984_);
                    v___x_5986_ = v_reuseFailAlloc_5987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg___boxed(
    mut v_msg_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(
        v_msg_5989_,
        v___y_5990_,
        v___y_5991_,
        v___y_5992_,
        v___y_5993_,
    );
    crate::leanh::lean_dec(v___y_5993_);
    crate::leanh::lean_dec_ref(v___y_5992_);
    crate::leanh::lean_dec(v___y_5991_);
    crate::leanh::lean_dec_ref(v___y_5990_);
    return v_res_5995_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v_isExporting_5997_: u8,
    mut v___x_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___x_6000_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6014_: u8 = 0;
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6033_: u8 = 0;
    let mut v_unused_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_unused_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6003_ = lean_st_ref_take(v___y_5996_);
                v_env_6004_ = crate::leanh::lean_ctor_get(v___x_6003_, 0);
                v_nextMacroScope_6005_ = crate::leanh::lean_ctor_get(v___x_6003_, 1);
                v_ngen_6006_ = crate::leanh::lean_ctor_get(v___x_6003_, 2);
                v_auxDeclNGen_6007_ = crate::leanh::lean_ctor_get(v___x_6003_, 3);
                v_traceState_6008_ = crate::leanh::lean_ctor_get(v___x_6003_, 4);
                v_messages_6009_ = crate::leanh::lean_ctor_get(v___x_6003_, 6);
                v_infoState_6010_ = crate::leanh::lean_ctor_get(v___x_6003_, 7);
                v_snapshotTasks_6011_ = crate::leanh::lean_ctor_get(v___x_6003_, 8);
                v_isSharedCheck_6036_ = (!crate::leanh::lean_is_exclusive(v___x_6003_)) as u8;
                if v_isSharedCheck_6036_ == 0 {
                    v_unused_6037_ = crate::leanh::lean_ctor_get(v___x_6003_, 5);
                    crate::leanh::lean_dec(v_unused_6037_);
                    v___x_6013_ = v___x_6003_;
                    v_isShared_6014_ = v_isSharedCheck_6036_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6011_);
                    crate::leanh::lean_inc(v_infoState_6010_);
                    crate::leanh::lean_inc(v_messages_6009_);
                    crate::leanh::lean_inc(v_traceState_6008_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6007_);
                    crate::leanh::lean_inc(v_ngen_6006_);
                    crate::leanh::lean_inc(v_nextMacroScope_6005_);
                    crate::leanh::lean_inc(v_env_6004_);
                    crate::leanh::lean_dec(v___x_6003_);
                    v___x_6013_ = crate::leanh::lean_box(0);
                    v_isShared_6014_ = v_isSharedCheck_6036_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6015_ = l_Lean_Environment_setExporting(v_env_6004_, v_isExporting_5997_);
                if v_isShared_6014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6013_, 5, v___x_5998_);
                    crate::leanh::lean_ctor_set(v___x_6013_, 0, v___x_6015_);
                    v___x_6017_ = v___x_6013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6035_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 1, v_nextMacroScope_6005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 2, v_ngen_6006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 3, v_auxDeclNGen_6007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 4, v_traceState_6008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 5, v___x_5998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 6, v_messages_6009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 7, v_infoState_6010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6035_, 8, v_snapshotTasks_6011_);
                    v___x_6017_ = v_reuseFailAlloc_6035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6018_ = lean_st_ref_set(v___y_5996_, v___x_6017_);
                v___x_6019_ = lean_st_ref_take(v___y_5999_);
                v_mctx_6020_ = crate::leanh::lean_ctor_get(v___x_6019_, 0);
                v_zetaDeltaFVarIds_6021_ = crate::leanh::lean_ctor_get(v___x_6019_, 2);
                v_postponed_6022_ = crate::leanh::lean_ctor_get(v___x_6019_, 3);
                v_diag_6023_ = crate::leanh::lean_ctor_get(v___x_6019_, 4);
                v_isSharedCheck_6033_ = (!crate::leanh::lean_is_exclusive(v___x_6019_)) as u8;
                if v_isSharedCheck_6033_ == 0 {
                    v_unused_6034_ = crate::leanh::lean_ctor_get(v___x_6019_, 1);
                    crate::leanh::lean_dec(v_unused_6034_);
                    v___x_6025_ = v___x_6019_;
                    v_isShared_6026_ = v_isSharedCheck_6033_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6023_);
                    crate::leanh::lean_inc(v_postponed_6022_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6021_);
                    crate::leanh::lean_inc(v_mctx_6020_);
                    crate::leanh::lean_dec(v___x_6019_);
                    v___x_6025_ = crate::leanh::lean_box(0);
                    v_isShared_6026_ = v_isSharedCheck_6033_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6025_, 1, v___x_6000_);
                    v___x_6028_ = v___x_6025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6032_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 0, v_mctx_6020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 1, v___x_6000_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6032_,
                        2,
                        v_zetaDeltaFVarIds_6021_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 3, v_postponed_6022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 4, v_diag_6023_);
                    v___x_6028_ = v_reuseFailAlloc_6032_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6029_ = lean_st_ref_set(v___y_5999_, v___x_6028_);
                v___x_6030_ = crate::leanh::lean_box(0);
                v___x_6031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6031_, 0, v___x_6030_);
                return v___x_6031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_6038_: *mut crate::leanh::LeanObject,
    mut v_isExporting_6039_: *mut crate::leanh::LeanObject,
    mut v___x_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___x_6042_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_6045_: u8 = 0;
    let mut v_res_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6045_ = (crate::leanh::lean_unbox(v_isExporting_6039_) as u8);
    v_res_6046_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_6038_, v_isExporting_boxed_6045_, v___x_6040_, v___y_6041_, v___x_6042_, v_a_x3f_6043_);
    crate::leanh::lean_dec(v_a_x3f_6043_);
    crate::leanh::lean_dec(v___y_6041_);
    crate::leanh::lean_dec(v___y_6038_);
    return v_res_6046_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(
    mut v_x_6047_: *mut crate::leanh::LeanObject,
    mut v_isExporting_6048_: u8,
    mut v___y_6049_: *mut crate::leanh::LeanObject,
    mut v___y_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6056_: u8 = 0;
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6068_: u8 = 0;
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6081_: u8 = 0;
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6090_: u8 = 0;
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6096_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6100_: u8 = 0;
    let mut v_unused_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6103_: u8 = 0;
    let mut v_a_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6113_: u8 = 0;
    let mut v_unused_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6116_: u8 = 0;
    let mut v_unused_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6054_ = lean_st_ref_get(v___y_6052_);
                v_env_6055_ = crate::leanh::lean_ctor_get(v___x_6054_, 0);
                crate::leanh::lean_inc_ref(v_env_6055_);
                crate::leanh::lean_dec(v___x_6054_);
                v_isExporting_6056_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_6055_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_6055_);
                v___x_6057_ = lean_st_ref_take(v___y_6052_);
                v_env_6058_ = crate::leanh::lean_ctor_get(v___x_6057_, 0);
                v_nextMacroScope_6059_ = crate::leanh::lean_ctor_get(v___x_6057_, 1);
                v_ngen_6060_ = crate::leanh::lean_ctor_get(v___x_6057_, 2);
                v_auxDeclNGen_6061_ = crate::leanh::lean_ctor_get(v___x_6057_, 3);
                v_traceState_6062_ = crate::leanh::lean_ctor_get(v___x_6057_, 4);
                v_messages_6063_ = crate::leanh::lean_ctor_get(v___x_6057_, 6);
                v_infoState_6064_ = crate::leanh::lean_ctor_get(v___x_6057_, 7);
                v_snapshotTasks_6065_ = crate::leanh::lean_ctor_get(v___x_6057_, 8);
                v_isSharedCheck_6119_ = (!crate::leanh::lean_is_exclusive(v___x_6057_)) as u8;
                if v_isSharedCheck_6119_ == 0 {
                    v_unused_6120_ = crate::leanh::lean_ctor_get(v___x_6057_, 5);
                    crate::leanh::lean_dec(v_unused_6120_);
                    v___x_6067_ = v___x_6057_;
                    v_isShared_6068_ = v_isSharedCheck_6119_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6065_);
                    crate::leanh::lean_inc(v_infoState_6064_);
                    crate::leanh::lean_inc(v_messages_6063_);
                    crate::leanh::lean_inc(v_traceState_6062_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6061_);
                    crate::leanh::lean_inc(v_ngen_6060_);
                    crate::leanh::lean_inc(v_nextMacroScope_6059_);
                    crate::leanh::lean_inc(v_env_6058_);
                    crate::leanh::lean_dec(v___x_6057_);
                    v___x_6067_ = crate::leanh::lean_box(0);
                    v_isShared_6068_ = v_isSharedCheck_6119_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6069_ = l_Lean_Environment_setExporting(v_env_6058_, v_isExporting_6048_);
                v___x_6070_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_withEqnOptions___redArg___closed__2_once),
                    _init_l_Lean_Meta_withEqnOptions___redArg___closed__2,
                );
                if v_isShared_6068_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6067_, 5, v___x_6070_);
                    crate::leanh::lean_ctor_set(v___x_6067_, 0, v___x_6069_);
                    v___x_6072_ = v___x_6067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6118_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 0, v___x_6069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 1, v_nextMacroScope_6059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 2, v_ngen_6060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 3, v_auxDeclNGen_6061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 4, v_traceState_6062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 5, v___x_6070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 6, v_messages_6063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 7, v_infoState_6064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6118_, 8, v_snapshotTasks_6065_);
                    v___x_6072_ = v_reuseFailAlloc_6118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6073_ = lean_st_ref_set(v___y_6052_, v___x_6072_);
                v___x_6074_ = lean_st_ref_take(v___y_6050_);
                v_mctx_6075_ = crate::leanh::lean_ctor_get(v___x_6074_, 0);
                v_zetaDeltaFVarIds_6076_ = crate::leanh::lean_ctor_get(v___x_6074_, 2);
                v_postponed_6077_ = crate::leanh::lean_ctor_get(v___x_6074_, 3);
                v_diag_6078_ = crate::leanh::lean_ctor_get(v___x_6074_, 4);
                v_isSharedCheck_6116_ = (!crate::leanh::lean_is_exclusive(v___x_6074_)) as u8;
                if v_isSharedCheck_6116_ == 0 {
                    v_unused_6117_ = crate::leanh::lean_ctor_get(v___x_6074_, 1);
                    crate::leanh::lean_dec(v_unused_6117_);
                    v___x_6080_ = v___x_6074_;
                    v_isShared_6081_ = v_isSharedCheck_6116_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6078_);
                    crate::leanh::lean_inc(v_postponed_6077_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6076_);
                    crate::leanh::lean_inc(v_mctx_6075_);
                    crate::leanh::lean_dec(v___x_6074_);
                    v___x_6080_ = crate::leanh::lean_box(0);
                    v_isShared_6081_ = v_isSharedCheck_6116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6082_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_saveEqnAffectingOptions___closed__2_once),
                    _init_l_Lean_Meta_saveEqnAffectingOptions___closed__2,
                );
                if v_isShared_6081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6080_, 1, v___x_6082_);
                    v___x_6084_ = v___x_6080_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6115_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 0, v_mctx_6075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 1, v___x_6082_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6115_,
                        2,
                        v_zetaDeltaFVarIds_6076_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 3, v_postponed_6077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 4, v_diag_6078_);
                    v___x_6084_ = v_reuseFailAlloc_6115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6085_ = lean_st_ref_set(v___y_6050_, v___x_6084_);
                crate::leanh::lean_inc(v___y_6052_);
                crate::leanh::lean_inc_ref(v___y_6051_);
                crate::leanh::lean_inc(v___y_6050_);
                crate::leanh::lean_inc_ref(v___y_6049_);
                v_r_6086_ = crate::leanh::lean_apply_5(
                    v_x_6047_,
                    v___y_6049_,
                    v___y_6050_,
                    v___y_6051_,
                    v___y_6052_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_6086_) == 0 {
                    v_a_6087_ = crate::leanh::lean_ctor_get(v_r_6086_, 0);
                    v_isSharedCheck_6103_ = (!crate::leanh::lean_is_exclusive(v_r_6086_)) as u8;
                    if v_isSharedCheck_6103_ == 0 {
                        v___x_6089_ = v_r_6086_;
                        v_isShared_6090_ = v_isSharedCheck_6103_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6087_);
                        crate::leanh::lean_dec(v_r_6086_);
                        v___x_6089_ = crate::leanh::lean_box(0);
                        v_isShared_6090_ = v_isSharedCheck_6103_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_6104_ = crate::leanh::lean_ctor_get(v_r_6086_, 0);
                    crate::leanh::lean_inc(v_a_6104_);
                    crate::leanh::lean_dec_ref_known(v_r_6086_, 1);
                    v___x_6105_ = crate::leanh::lean_box(0);
                    v___x_6106_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_6052_, v_isExporting_6056_, v___x_6070_, v___y_6050_, v___x_6082_, v___x_6105_);
                    v_isSharedCheck_6113_ = (!crate::leanh::lean_is_exclusive(v___x_6106_)) as u8;
                    if v_isSharedCheck_6113_ == 0 {
                        v_unused_6114_ = crate::leanh::lean_ctor_get(v___x_6106_, 0);
                        crate::leanh::lean_dec(v_unused_6114_);
                        v___x_6108_ = v___x_6106_;
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6106_);
                        v___x_6108_ = crate::leanh::lean_box(0);
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_6087_);
                if v_isShared_6090_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6089_, 1);
                    v___x_6092_ = v___x_6089_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6087_);
                    v___x_6092_ = v_reuseFailAlloc_6102_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6093_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___lam__0(v___y_6052_, v_isExporting_6056_, v___x_6070_, v___y_6050_, v___x_6082_, v___x_6092_);
                crate::leanh::lean_dec_ref(v___x_6092_);
                v_isSharedCheck_6100_ = (!crate::leanh::lean_is_exclusive(v___x_6093_)) as u8;
                if v_isSharedCheck_6100_ == 0 {
                    v_unused_6101_ = crate::leanh::lean_ctor_get(v___x_6093_, 0);
                    crate::leanh::lean_dec(v_unused_6101_);
                    v___x_6095_ = v___x_6093_;
                    v_isShared_6096_ = v_isSharedCheck_6100_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6093_);
                    v___x_6095_ = crate::leanh::lean_box(0);
                    v_isShared_6096_ = v_isSharedCheck_6100_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6095_, 0, v_a_6087_);
                    v___x_6098_ = v___x_6095_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6099_, 0, v_a_6087_);
                    v___x_6098_ = v_reuseFailAlloc_6099_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6098_;
            }
            9 => {
                if v_isShared_6109_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6108_, 1);
                    crate::leanh::lean_ctor_set(v___x_6108_, 0, v_a_6104_);
                    v___x_6111_ = v___x_6108_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6104_);
                    v___x_6111_ = v_reuseFailAlloc_6112_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_6121_: *mut crate::leanh::LeanObject,
    mut v_isExporting_6122_: *mut crate::leanh::LeanObject,
    mut v___y_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
    mut v___y_6125_: *mut crate::leanh::LeanObject,
    mut v___y_6126_: *mut crate::leanh::LeanObject,
    mut v___y_6127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_6128_: u8 = 0;
    let mut v_res_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6128_ = (crate::leanh::lean_unbox(v_isExporting_6122_) as u8);
    v_res_6129_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_6121_, v_isExporting_boxed_6128_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
    crate::leanh::lean_dec(v___y_6126_);
    crate::leanh::lean_dec_ref(v___y_6125_);
    crate::leanh::lean_dec(v___y_6124_);
    crate::leanh::lean_dec_ref(v___y_6123_);
    return v_res_6129_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(
    mut v_x_6130_: *mut crate::leanh::LeanObject,
    mut v_when_6131_: u8,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_6131_ == 0 {
        let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_6135_);
        crate::leanh::lean_inc_ref(v___y_6134_);
        crate::leanh::lean_inc(v___y_6133_);
        crate::leanh::lean_inc_ref(v___y_6132_);
        v___x_6137_ = crate::leanh::lean_apply_5(
            v_x_6130_,
            v___y_6132_,
            v___y_6133_,
            v___y_6134_,
            v___y_6135_,
            crate::leanh::lean_box(0),
        );
        return v___x_6137_;
    } else {
        let mut v___x_6138_: u8 = 0;
        let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6138_ = 0;
        v___x_6139_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_6130_, v___x_6138_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
        return v___x_6139_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg___boxed(
    mut v_x_6140_: *mut crate::leanh::LeanObject,
    mut v_when_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_6147_: u8 = 0;
    let mut v_res_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_6147_ = (crate::leanh::lean_unbox(v_when_6141_) as u8);
    v_res_6148_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(
        v_x_6140_,
        v_when_boxed_6147_,
        v___y_6142_,
        v___y_6143_,
        v___y_6144_,
        v___y_6145_,
    );
    crate::leanh::lean_dec(v___y_6145_);
    crate::leanh::lean_dec_ref(v___y_6144_);
    crate::leanh::lean_dec(v___y_6143_);
    crate::leanh::lean_dec_ref(v___y_6142_);
    return v_res_6148_;
}
pub unsafe fn _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6150_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0;
    v___x_6151_ = l_Lean_stringToMessageData(v___x_6150_);
    return v___x_6151_;
}
pub unsafe fn _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6153_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2;
    v___x_6154_ = l_Lean_stringToMessageData(v___x_6153_);
    return v___x_6154_;
}
pub unsafe fn _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6156_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4;
    v___x_6157_ = l_Lean_stringToMessageData(v___x_6156_);
    return v___x_6157_;
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(
    mut v_declName_6158_: *mut crate::leanh::LeanObject,
    mut v_nonRec_6159_: u8,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: u8 = 0;
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: u8 = 0;
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6165_ = lean_st_ref_get(v___y_6163_);
                v_env_6166_ = crate::leanh::lean_ctor_get(v___x_6165_, 0);
                crate::leanh::lean_inc_ref(v_env_6166_);
                crate::leanh::lean_dec(v___x_6165_);
                v___x_6167_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                crate::leanh::lean_inc(v_declName_6158_);
                v___x_6168_ =
                    l_Lean_Meta_mkEqLikeNameFor(v_env_6166_, v_declName_6158_, v___x_6167_);
                v___x_6169_ = crate::leanh::lean_box((v_nonRec_6159_) as usize);
                crate::leanh::lean_inc(v___x_6168_);
                v___f_6170_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_6170_, 0, v___x_6168_);
                crate::leanh::lean_closure_set(v___f_6170_, 1, v_declName_6158_);
                crate::leanh::lean_closure_set(v___f_6170_, 2, v___x_6169_);
                crate::leanh::lean_closure_set(v___f_6170_, 3, v___x_6167_);
                v___x_6171_ = 1;
                v___x_6172_ =
                    l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(
                        v___f_6170_,
                        v___x_6171_,
                        v___y_6160_,
                        v___y_6161_,
                        v___y_6162_,
                        v___y_6163_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6172_) == 0 {
                    v_a_6173_ = crate::leanh::lean_ctor_get(v___x_6172_, 0);
                    crate::leanh::lean_inc(v_a_6173_);
                    if crate::leanh::lean_obj_tag(v_a_6173_) == 1 {
                        v_val_6174_ = crate::leanh::lean_ctor_get(v_a_6173_, 0);
                        crate::leanh::lean_inc(v_val_6174_);
                        crate::leanh::lean_dec_ref_known(v_a_6173_, 1);
                        v___x_6175_ = lean_name_eq(v_val_6174_, v___x_6168_);
                        if v___x_6175_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6172_, 1);
                            v___x_6176_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1_once
                                ),
                                _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1,
                            );
                            v___x_6177_ = l_Lean_MessageData_ofName(v_val_6174_);
                            v___x_6178_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6178_, 0, v___x_6176_);
                            crate::leanh::lean_ctor_set(v___x_6178_, 1, v___x_6177_);
                            v___x_6179_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3_once
                                ),
                                _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3,
                            );
                            v___x_6180_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6180_, 0, v___x_6178_);
                            crate::leanh::lean_ctor_set(v___x_6180_, 1, v___x_6179_);
                            v___x_6181_ = l_Lean_MessageData_ofName(v___x_6168_);
                            v___x_6182_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6182_, 0, v___x_6180_);
                            crate::leanh::lean_ctor_set(v___x_6182_, 1, v___x_6181_);
                            v___x_6183_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5_once
                                ),
                                _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5,
                            );
                            v___x_6184_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6184_, 0, v___x_6182_);
                            crate::leanh::lean_ctor_set(v___x_6184_, 1, v___x_6183_);
                            v___x_6185_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(v___x_6184_, v___y_6160_, v___y_6161_, v___y_6162_, v___y_6163_);
                            v_a_6186_ = crate::leanh::lean_ctor_get(v___x_6185_, 0);
                            v_isSharedCheck_6193_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6185_)) as u8;
                            if v_isSharedCheck_6193_ == 0 {
                                v___x_6188_ = v___x_6185_;
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6186_);
                                crate::leanh::lean_dec(v___x_6185_);
                                v___x_6188_ = crate::leanh::lean_box(0);
                                v_isShared_6189_ = v_isSharedCheck_6193_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_6174_);
                            crate::leanh::lean_dec(v___x_6168_);
                            return v___x_6172_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6173_);
                        crate::leanh::lean_dec(v___x_6168_);
                        return v___x_6172_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6168_);
                    return v___x_6172_;
                }
            }
            1 => {
                if v_isShared_6189_ == 0 {
                    v___x_6191_ = v___x_6188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(
    mut v_declName_6194_: *mut crate::leanh::LeanObject,
    mut v_nonRec_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
    mut v___y_6200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nonRec_boxed_6201_: u8 = 0;
    let mut v_res_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nonRec_boxed_6201_ = (crate::leanh::lean_unbox(v_nonRec_6195_) as u8);
    v_res_6202_ = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(
        v_declName_6194_,
        v_nonRec_boxed_6201_,
        v___y_6196_,
        v___y_6197_,
        v___y_6198_,
        v___y_6199_,
    );
    crate::leanh::lean_dec(v___y_6199_);
    crate::leanh::lean_dec_ref(v___y_6198_);
    crate::leanh::lean_dec(v___y_6197_);
    crate::leanh::lean_dec_ref(v___y_6196_);
    return v_res_6202_;
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f(
    mut v_declName_6203_: *mut crate::leanh::LeanObject,
    mut v_nonRec_6204_: u8,
    mut v_a_6205_: *mut crate::leanh::LeanObject,
    mut v_a_6206_: *mut crate::leanh::LeanObject,
    mut v_a_6207_: *mut crate::leanh::LeanObject,
    mut v_a_6208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6210_ = crate::leanh::lean_box((v_nonRec_6204_) as usize);
    v___f_6211_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6211_, 0, v_declName_6203_);
    crate::leanh::lean_closure_set(v___f_6211_, 1, v___x_6210_);
    v___x_6212_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6213_ = lean_mk_empty_array_with_capacity(v___x_6212_);
    crate::leanh::lean_dec_ref(v___x_6213_);
    v___x_6214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2,
    );
    v___x_6215_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
    v___x_6216_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__1___redArg(v___x_6214_, v___x_6215_, v___f_6211_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_);
    return v___x_6216_;
}
pub unsafe fn l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(
    mut v_declName_6217_: *mut crate::leanh::LeanObject,
    mut v_nonRec_6218_: *mut crate::leanh::LeanObject,
    mut v_a_6219_: *mut crate::leanh::LeanObject,
    mut v_a_6220_: *mut crate::leanh::LeanObject,
    mut v_a_6221_: *mut crate::leanh::LeanObject,
    mut v_a_6222_: *mut crate::leanh::LeanObject,
    mut v_a_6223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nonRec_boxed_6224_: u8 = 0;
    let mut v_res_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nonRec_boxed_6224_ = (crate::leanh::lean_unbox(v_nonRec_6218_) as u8);
    v_res_6225_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
        v_declName_6217_,
        v_nonRec_boxed_6224_,
        v_a_6219_,
        v_a_6220_,
        v_a_6221_,
        v_a_6222_,
    );
    crate::leanh::lean_dec(v_a_6222_);
    crate::leanh::lean_dec_ref(v_a_6221_);
    crate::leanh::lean_dec(v_a_6220_);
    crate::leanh::lean_dec_ref(v_a_6219_);
    return v_res_6225_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(
    mut v_declName_6226_: *mut crate::leanh::LeanObject,
    mut v_as_6227_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6228_: *mut crate::leanh::LeanObject,
    mut v_b_6229_: *mut crate::leanh::LeanObject,
    mut v_a_6230_: *mut crate::leanh::LeanObject,
    mut v___y_6231_: *mut crate::leanh::LeanObject,
    mut v___y_6232_: *mut crate::leanh::LeanObject,
    mut v___y_6233_: *mut crate::leanh::LeanObject,
    mut v___y_6234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6236_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(
        v_declName_6226_,
        v_as_x27_6228_,
        v_b_6229_,
        v___y_6231_,
        v___y_6232_,
        v___y_6233_,
        v___y_6234_,
    );
    return v___x_6236_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(
    mut v_declName_6237_: *mut crate::leanh::LeanObject,
    mut v_as_6238_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6239_: *mut crate::leanh::LeanObject,
    mut v_b_6240_: *mut crate::leanh::LeanObject,
    mut v_a_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6247_ = l_List_forIn_x27_loop___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__0(
        v_declName_6237_,
        v_as_6238_,
        v_as_x27_6239_,
        v_b_6240_,
        v_a_6241_,
        v___y_6242_,
        v___y_6243_,
        v___y_6244_,
        v___y_6245_,
    );
    crate::leanh::lean_dec(v___y_6245_);
    crate::leanh::lean_dec_ref(v___y_6244_);
    crate::leanh::lean_dec(v___y_6243_);
    crate::leanh::lean_dec_ref(v___y_6242_);
    crate::leanh::lean_dec(v_as_x27_6239_);
    crate::leanh::lean_dec(v_as_6238_);
    return v_res_6247_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(
    mut v_00_u03b1_6248_: *mut crate::leanh::LeanObject,
    mut v_x_6249_: *mut crate::leanh::LeanObject,
    mut v_isExporting_6250_: u8,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6256_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___redArg(v_x_6249_, v_isExporting_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_);
    return v___x_6256_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b1_6257_: *mut crate::leanh::LeanObject,
    mut v_x_6258_: *mut crate::leanh::LeanObject,
    mut v_isExporting_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
    mut v___y_6264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_6265_: u8 = 0;
    let mut v_res_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6265_ = (crate::leanh::lean_unbox(v_isExporting_6259_) as u8);
    v_res_6266_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1_spec__1(v_00_u03b1_6257_, v_x_6258_, v_isExporting_boxed_6265_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
    crate::leanh::lean_dec(v___y_6263_);
    crate::leanh::lean_dec_ref(v___y_6262_);
    crate::leanh::lean_dec(v___y_6261_);
    crate::leanh::lean_dec_ref(v___y_6260_);
    return v_res_6266_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(
    mut v_00_u03b1_6267_: *mut crate::leanh::LeanObject,
    mut v_x_6268_: *mut crate::leanh::LeanObject,
    mut v_when_6269_: u8,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6275_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___redArg(
        v_x_6268_,
        v_when_6269_,
        v___y_6270_,
        v___y_6271_,
        v___y_6272_,
        v___y_6273_,
    );
    return v___x_6275_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1___boxed(
    mut v_00_u03b1_6276_: *mut crate::leanh::LeanObject,
    mut v_x_6277_: *mut crate::leanh::LeanObject,
    mut v_when_6278_: *mut crate::leanh::LeanObject,
    mut v___y_6279_: *mut crate::leanh::LeanObject,
    mut v___y_6280_: *mut crate::leanh::LeanObject,
    mut v___y_6281_: *mut crate::leanh::LeanObject,
    mut v___y_6282_: *mut crate::leanh::LeanObject,
    mut v___y_6283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_6284_: u8 = 0;
    let mut v_res_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_6284_ = (crate::leanh::lean_unbox(v_when_6278_) as u8);
    v_res_6285_ = l_Lean_withoutExporting___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__1(
        v_00_u03b1_6276_,
        v_x_6277_,
        v_when_boxed_6284_,
        v___y_6279_,
        v___y_6280_,
        v___y_6281_,
        v___y_6282_,
    );
    crate::leanh::lean_dec(v___y_6282_);
    crate::leanh::lean_dec_ref(v___y_6281_);
    crate::leanh::lean_dec(v___y_6280_);
    crate::leanh::lean_dec_ref(v___y_6279_);
    return v_res_6285_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(
    mut v_00_u03b1_6286_: *mut crate::leanh::LeanObject,
    mut v_msg_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
    mut v___y_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6293_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___redArg(
        v_msg_6287_,
        v___y_6288_,
        v___y_6289_,
        v___y_6290_,
        v___y_6291_,
    );
    return v___x_6293_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2___boxed(
    mut v_00_u03b1_6294_: *mut crate::leanh::LeanObject,
    mut v_msg_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6301_ = l_Lean_throwError___at___00Lean_Meta_getUnfoldEqnFor_x3f_spec__2(
        v_00_u03b1_6294_,
        v_msg_6295_,
        v___y_6296_,
        v___y_6297_,
        v___y_6298_,
        v___y_6299_,
    );
    crate::leanh::lean_dec(v___y_6299_);
    crate::leanh::lean_dec_ref(v___y_6298_);
    crate::leanh::lean_dec(v___y_6297_);
    crate::leanh::lean_dec_ref(v___y_6296_);
    return v_res_6301_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6302_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6303_ = lean_mk_empty_array_with_capacity(v___x_6302_);
    v___x_6304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6304_, 0, v___x_6303_);
    return v___x_6304_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6305_: usize = 0;
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6305_ = 5usize;
    v___x_6306_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6307_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6308_ = lean_mk_empty_array_with_capacity(v___x_6307_);
    v___x_6309_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__0);
    v___x_6310_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6310_, 0, v___x_6309_);
    crate::leanh::lean_ctor_set(v___x_6310_, 1, v___x_6308_);
    crate::leanh::lean_ctor_set(v___x_6310_, 2, v___x_6306_);
    crate::leanh::lean_ctor_set(v___x_6310_, 3, v___x_6306_);
    crate::leanh::lean_ctor_set_usize(v___x_6310_, 4, v___x_6305_);
    return v___x_6310_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(
    mut v___y_6311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_6315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6328_: u8 = 0;
    let mut v_tid_6329_: u64 = 0;
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6332_: u8 = 0;
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_unused_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6313_ = lean_st_ref_get(v___y_6311_);
                v_traceState_6314_ = crate::leanh::lean_ctor_get(v___x_6313_, 4);
                crate::leanh::lean_inc_ref(v_traceState_6314_);
                crate::leanh::lean_dec(v___x_6313_);
                v_traces_6315_ = crate::leanh::lean_ctor_get(v_traceState_6314_, 0);
                crate::leanh::lean_inc_ref(v_traces_6315_);
                crate::leanh::lean_dec_ref(v_traceState_6314_);
                v___x_6316_ = lean_st_ref_take(v___y_6311_);
                v_traceState_6317_ = crate::leanh::lean_ctor_get(v___x_6316_, 4);
                v_env_6318_ = crate::leanh::lean_ctor_get(v___x_6316_, 0);
                v_nextMacroScope_6319_ = crate::leanh::lean_ctor_get(v___x_6316_, 1);
                v_ngen_6320_ = crate::leanh::lean_ctor_get(v___x_6316_, 2);
                v_auxDeclNGen_6321_ = crate::leanh::lean_ctor_get(v___x_6316_, 3);
                v_cache_6322_ = crate::leanh::lean_ctor_get(v___x_6316_, 5);
                v_messages_6323_ = crate::leanh::lean_ctor_get(v___x_6316_, 6);
                v_infoState_6324_ = crate::leanh::lean_ctor_get(v___x_6316_, 7);
                v_snapshotTasks_6325_ = crate::leanh::lean_ctor_get(v___x_6316_, 8);
                v_isSharedCheck_6344_ = (!crate::leanh::lean_is_exclusive(v___x_6316_)) as u8;
                if v_isSharedCheck_6344_ == 0 {
                    v___x_6327_ = v___x_6316_;
                    v_isShared_6328_ = v_isSharedCheck_6344_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6325_);
                    crate::leanh::lean_inc(v_infoState_6324_);
                    crate::leanh::lean_inc(v_messages_6323_);
                    crate::leanh::lean_inc(v_cache_6322_);
                    crate::leanh::lean_inc(v_traceState_6317_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6321_);
                    crate::leanh::lean_inc(v_ngen_6320_);
                    crate::leanh::lean_inc(v_nextMacroScope_6319_);
                    crate::leanh::lean_inc(v_env_6318_);
                    crate::leanh::lean_dec(v___x_6316_);
                    v___x_6327_ = crate::leanh::lean_box(0);
                    v_isShared_6328_ = v_isSharedCheck_6344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_6329_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6342_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6317_)) as u8;
                if v_isSharedCheck_6342_ == 0 {
                    v_unused_6343_ = crate::leanh::lean_ctor_get(v_traceState_6317_, 0);
                    crate::leanh::lean_dec(v_unused_6343_);
                    v___x_6331_ = v_traceState_6317_;
                    v_isShared_6332_ = v_isSharedCheck_6342_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_6317_);
                    v___x_6331_ = crate::leanh::lean_box(0);
                    v_isShared_6332_ = v_isSharedCheck_6342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___closed__1);
                if v_isShared_6332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6331_, 0, v___x_6333_);
                    v___x_6335_ = v___x_6331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___x_6333_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6341_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6329_,
                    );
                    v___x_6335_ = v_reuseFailAlloc_6341_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6327_, 4, v___x_6335_);
                    v___x_6337_ = v___x_6327_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6340_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 0, v_env_6318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 1, v_nextMacroScope_6319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 2, v_ngen_6320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 3, v_auxDeclNGen_6321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 4, v___x_6335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 5, v_cache_6322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 6, v_messages_6323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 7, v_infoState_6324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6340_, 8, v_snapshotTasks_6325_);
                    v___x_6337_ = v_reuseFailAlloc_6340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6338_ = lean_st_ref_set(v___y_6311_, v___x_6337_);
                v___x_6339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6339_, 0, v_traces_6315_);
                return v___x_6339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v___y_6345_: *mut crate::leanh::LeanObject,
    mut v___y_6346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6347_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_6345_);
    crate::leanh::lean_dec(v___y_6345_);
    return v_res_6347_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(
    mut v___y_6348_: *mut crate::leanh::LeanObject,
    mut v___y_6349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6351_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_6349_);
    return v___x_6351_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___boxed(
    mut v___y_6352_: *mut crate::leanh::LeanObject,
    mut v___y_6353_: *mut crate::leanh::LeanObject,
    mut v___y_6354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6355_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0(v___y_6352_, v___y_6353_);
    crate::leanh::lean_dec(v___y_6353_);
    crate::leanh::lean_dec_ref(v___y_6352_);
    return v_res_6355_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(
    mut v_____r_6356_: *mut crate::leanh::LeanObject,
    mut v___y_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6360_: u8 = 0;
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6360_ = 0;
    v___x_6361_ = crate::leanh::lean_box((v___x_6360_) as usize);
    v___x_6362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6362_, 0, v___x_6361_);
    return v___x_6362_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(
    mut v_____r_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6367_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_____r_6363_, v___y_6364_, v___y_6365_);
    crate::leanh::lean_dec(v___y_6365_);
    crate::leanh::lean_dec_ref(v___y_6364_);
    return v_res_6367_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_6370_ = l_Lean_stringToMessageData(v___x_6369_);
    return v___x_6370_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(
    mut v_name_6371_: *mut crate::leanh::LeanObject,
    mut v_x_6372_: *mut crate::leanh::LeanObject,
    mut v___y_6373_: *mut crate::leanh::LeanObject,
    mut v___y_6374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_6377_ = l_Lean_MessageData_ofName(v_name_6371_);
    v___x_6378_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6378_, 0, v___x_6376_);
    crate::leanh::lean_ctor_set(v___x_6378_, 1, v___x_6377_);
    v___x_6379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6379_, 0, v___x_6378_);
    return v___x_6379_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(
    mut v_name_6380_: *mut crate::leanh::LeanObject,
    mut v_x_6381_: *mut crate::leanh::LeanObject,
    mut v___y_6382_: *mut crate::leanh::LeanObject,
    mut v___y_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6385_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v_name_6380_, v_x_6381_, v___y_6382_, v___y_6383_);
    crate::leanh::lean_dec(v___y_6383_);
    crate::leanh::lean_dec_ref(v___y_6382_);
    crate::leanh::lean_dec_ref(v_x_6381_);
    return v_res_6385_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(
    mut v_x_6386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6391_: u8 = 0;
    let mut v___x_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6395_: u8 = 0;
    let mut v_a_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6399_: u8 = 0;
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6386_) == 0 {
                    v_a_6388_ = crate::leanh::lean_ctor_get(v_x_6386_, 0);
                    v_isSharedCheck_6395_ = (!crate::leanh::lean_is_exclusive(v_x_6386_)) as u8;
                    if v_isSharedCheck_6395_ == 0 {
                        v___x_6390_ = v_x_6386_;
                        v_isShared_6391_ = v_isSharedCheck_6395_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6388_);
                        crate::leanh::lean_dec(v_x_6386_);
                        v___x_6390_ = crate::leanh::lean_box(0);
                        v_isShared_6391_ = v_isSharedCheck_6395_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6396_ = crate::leanh::lean_ctor_get(v_x_6386_, 0);
                    v_isSharedCheck_6403_ = (!crate::leanh::lean_is_exclusive(v_x_6386_)) as u8;
                    if v_isSharedCheck_6403_ == 0 {
                        v___x_6398_ = v_x_6386_;
                        v_isShared_6399_ = v_isSharedCheck_6403_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6396_);
                        crate::leanh::lean_dec(v_x_6386_);
                        v___x_6398_ = crate::leanh::lean_box(0);
                        v_isShared_6399_ = v_isSharedCheck_6403_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6391_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6390_, 1);
                    v___x_6393_ = v___x_6390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6394_, 0, v_a_6388_);
                    v___x_6393_ = v_reuseFailAlloc_6394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6393_;
            }
            3 => {
                if v_isShared_6399_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6398_, 0);
                    v___x_6401_ = v___x_6398_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6402_, 0, v_a_6396_);
                    v___x_6401_ = v_reuseFailAlloc_6402_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(
    mut v_x_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6406_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_6404_);
    return v_res_6406_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(
    mut v_e_6407_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_e_6407_) == 0 {
        let mut v___x_6408_: u8 = 0;
        v___x_6408_ = 2;
        return v___x_6408_;
    } else {
        let mut v_a_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6410_: u8 = 0;
        v_a_6409_ = crate::leanh::lean_ctor_get(v_e_6407_, 0);
        v___x_6410_ = (crate::leanh::lean_unbox(v_a_6409_) as u8);
        if v___x_6410_ == 0 {
            let mut v___x_6411_: u8 = 0;
            v___x_6411_ = 1;
            return v___x_6411_;
        } else {
            let mut v___x_6412_: u8 = 0;
            v___x_6412_ = 0;
            return v___x_6412_;
        }
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_e_6413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6414_: u8 = 0;
    let mut v_r_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6414_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_e_6413_);
    crate::leanh::lean_dec_ref(v_e_6413_);
    v_r_6415_ = crate::leanh::lean_box((v_res_6414_) as usize);
    return v_r_6415_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(
    mut v_sz_6416_: usize,
    mut v_i_6417_: usize,
    mut v_bs_6418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6419_: u8 = 0;
    let mut v_v_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: usize = 0;
    let mut v___x_6425_: usize = 0;
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6419_ = lean_usize_dec_lt(v_i_6417_, v_sz_6416_);
                if v___x_6419_ == 0 {
                    return v_bs_6418_;
                } else {
                    v_v_6420_ = lean_array_uget_borrowed(v_bs_6418_, v_i_6417_);
                    v_msg_6421_ = crate::leanh::lean_ctor_get(v_v_6420_, 1);
                    crate::leanh::lean_inc_ref(v_msg_6421_);
                    v___x_6422_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6423_ = lean_array_uset(v_bs_6418_, v_i_6417_, v___x_6422_);
                    v___x_6424_ = 1usize;
                    v___x_6425_ = lean_usize_add(v_i_6417_, v___x_6424_);
                    v___x_6426_ = lean_array_uset(v_bs_x27_6423_, v_i_6417_, v_msg_6421_);
                    v_i_6417_ = v___x_6425_;
                    v_bs_6418_ = v___x_6426_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(
    mut v_sz_6428_: *mut crate::leanh::LeanObject,
    mut v_i_6429_: *mut crate::leanh::LeanObject,
    mut v_bs_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6431_: usize = 0;
    let mut v_i_boxed_6432_: usize = 0;
    let mut v_res_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6431_ = crate::leanh::lean_unbox_usize(v_sz_6428_);
    crate::leanh::lean_dec(v_sz_6428_);
    v_i_boxed_6432_ = crate::leanh::lean_unbox_usize(v_i_6429_);
    crate::leanh::lean_dec(v_i_6429_);
    v_res_6433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_boxed_6431_, v_i_boxed_6432_, v_bs_6430_);
    return v_res_6433_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(
    mut v_oldTraces_6434_: *mut crate::leanh::LeanObject,
    mut v_data_6435_: *mut crate::leanh::LeanObject,
    mut v_ref_6436_: *mut crate::leanh::LeanObject,
    mut v_msg_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6453_: u8 = 0;
    let mut v_cancelTk_x3f_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6455_: u8 = 0;
    let mut v_inheritedTraceOptions_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6463_: usize = 0;
    let mut v___x_6464_: usize = 0;
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6471_: u8 = 0;
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6484_: u8 = 0;
    let mut v_tid_6485_: u64 = 0;
    let mut v___x_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6488_: u8 = 0;
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6502_: u8 = 0;
    let mut v_unused_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6441_ = crate::leanh::lean_ctor_get(v___y_6438_, 0);
                v_fileMap_6442_ = crate::leanh::lean_ctor_get(v___y_6438_, 1);
                v_options_6443_ = crate::leanh::lean_ctor_get(v___y_6438_, 2);
                v_currRecDepth_6444_ = crate::leanh::lean_ctor_get(v___y_6438_, 3);
                v_maxRecDepth_6445_ = crate::leanh::lean_ctor_get(v___y_6438_, 4);
                v_ref_6446_ = crate::leanh::lean_ctor_get(v___y_6438_, 5);
                v_currNamespace_6447_ = crate::leanh::lean_ctor_get(v___y_6438_, 6);
                v_openDecls_6448_ = crate::leanh::lean_ctor_get(v___y_6438_, 7);
                v_initHeartbeats_6449_ = crate::leanh::lean_ctor_get(v___y_6438_, 8);
                v_maxHeartbeats_6450_ = crate::leanh::lean_ctor_get(v___y_6438_, 9);
                v_quotContext_6451_ = crate::leanh::lean_ctor_get(v___y_6438_, 10);
                v_currMacroScope_6452_ = crate::leanh::lean_ctor_get(v___y_6438_, 11);
                v_diag_6453_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6438_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6454_ = crate::leanh::lean_ctor_get(v___y_6438_, 12);
                v_suppressElabErrors_6455_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6438_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6456_ = crate::leanh::lean_ctor_get(v___y_6438_, 13);
                v___x_6457_ = lean_st_ref_get(v___y_6439_);
                v_traceState_6458_ = crate::leanh::lean_ctor_get(v___x_6457_, 4);
                crate::leanh::lean_inc_ref(v_traceState_6458_);
                crate::leanh::lean_dec(v___x_6457_);
                v_traces_6459_ = crate::leanh::lean_ctor_get(v_traceState_6458_, 0);
                crate::leanh::lean_inc_ref(v_traces_6459_);
                crate::leanh::lean_dec_ref(v_traceState_6458_);
                v_ref_6460_ = l_Lean_replaceRef(v_ref_6436_, v_ref_6446_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6456_);
                crate::leanh::lean_inc(v_cancelTk_x3f_6454_);
                crate::leanh::lean_inc(v_currMacroScope_6452_);
                crate::leanh::lean_inc(v_quotContext_6451_);
                crate::leanh::lean_inc(v_maxHeartbeats_6450_);
                crate::leanh::lean_inc(v_initHeartbeats_6449_);
                crate::leanh::lean_inc(v_openDecls_6448_);
                crate::leanh::lean_inc(v_currNamespace_6447_);
                crate::leanh::lean_inc(v_maxRecDepth_6445_);
                crate::leanh::lean_inc(v_currRecDepth_6444_);
                crate::leanh::lean_inc_ref(v_options_6443_);
                crate::leanh::lean_inc_ref(v_fileMap_6442_);
                crate::leanh::lean_inc_ref(v_fileName_6441_);
                v___x_6461_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_6461_, 0, v_fileName_6441_);
                crate::leanh::lean_ctor_set(v___x_6461_, 1, v_fileMap_6442_);
                crate::leanh::lean_ctor_set(v___x_6461_, 2, v_options_6443_);
                crate::leanh::lean_ctor_set(v___x_6461_, 3, v_currRecDepth_6444_);
                crate::leanh::lean_ctor_set(v___x_6461_, 4, v_maxRecDepth_6445_);
                crate::leanh::lean_ctor_set(v___x_6461_, 5, v_ref_6460_);
                crate::leanh::lean_ctor_set(v___x_6461_, 6, v_currNamespace_6447_);
                crate::leanh::lean_ctor_set(v___x_6461_, 7, v_openDecls_6448_);
                crate::leanh::lean_ctor_set(v___x_6461_, 8, v_initHeartbeats_6449_);
                crate::leanh::lean_ctor_set(v___x_6461_, 9, v_maxHeartbeats_6450_);
                crate::leanh::lean_ctor_set(v___x_6461_, 10, v_quotContext_6451_);
                crate::leanh::lean_ctor_set(v___x_6461_, 11, v_currMacroScope_6452_);
                crate::leanh::lean_ctor_set(v___x_6461_, 12, v_cancelTk_x3f_6454_);
                crate::leanh::lean_ctor_set(v___x_6461_, 13, v_inheritedTraceOptions_6456_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_6453_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6461_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6455_,
                );
                v___x_6462_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6459_);
                crate::leanh::lean_dec_ref(v_traces_6459_);
                v_sz_6463_ = lean_array_size(v___x_6462_);
                v___x_6464_ = 0usize;
                v___x_6465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_sz_6463_, v___x_6464_, v___x_6462_);
                v_msg_6466_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_msg_6466_, 0, v_data_6435_);
                crate::leanh::lean_ctor_set(v_msg_6466_, 1, v_msg_6437_);
                crate::leanh::lean_ctor_set(v_msg_6466_, 2, v___x_6465_);
                v___x_6467_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2(v_msg_6466_, v___x_6461_, v___y_6439_);
                crate::leanh::lean_dec_ref_known(v___x_6461_, 14);
                v_a_6468_ = crate::leanh::lean_ctor_get(v___x_6467_, 0);
                v_isSharedCheck_6505_ = (!crate::leanh::lean_is_exclusive(v___x_6467_)) as u8;
                if v_isSharedCheck_6505_ == 0 {
                    v___x_6470_ = v___x_6467_;
                    v_isShared_6471_ = v_isSharedCheck_6505_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6468_);
                    crate::leanh::lean_dec(v___x_6467_);
                    v___x_6470_ = crate::leanh::lean_box(0);
                    v_isShared_6471_ = v_isSharedCheck_6505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6472_ = lean_st_ref_take(v___y_6439_);
                v_traceState_6473_ = crate::leanh::lean_ctor_get(v___x_6472_, 4);
                v_env_6474_ = crate::leanh::lean_ctor_get(v___x_6472_, 0);
                v_nextMacroScope_6475_ = crate::leanh::lean_ctor_get(v___x_6472_, 1);
                v_ngen_6476_ = crate::leanh::lean_ctor_get(v___x_6472_, 2);
                v_auxDeclNGen_6477_ = crate::leanh::lean_ctor_get(v___x_6472_, 3);
                v_cache_6478_ = crate::leanh::lean_ctor_get(v___x_6472_, 5);
                v_messages_6479_ = crate::leanh::lean_ctor_get(v___x_6472_, 6);
                v_infoState_6480_ = crate::leanh::lean_ctor_get(v___x_6472_, 7);
                v_snapshotTasks_6481_ = crate::leanh::lean_ctor_get(v___x_6472_, 8);
                v_isSharedCheck_6504_ = (!crate::leanh::lean_is_exclusive(v___x_6472_)) as u8;
                if v_isSharedCheck_6504_ == 0 {
                    v___x_6483_ = v___x_6472_;
                    v_isShared_6484_ = v_isSharedCheck_6504_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6481_);
                    crate::leanh::lean_inc(v_infoState_6480_);
                    crate::leanh::lean_inc(v_messages_6479_);
                    crate::leanh::lean_inc(v_cache_6478_);
                    crate::leanh::lean_inc(v_traceState_6473_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6477_);
                    crate::leanh::lean_inc(v_ngen_6476_);
                    crate::leanh::lean_inc(v_nextMacroScope_6475_);
                    crate::leanh::lean_inc(v_env_6474_);
                    crate::leanh::lean_dec(v___x_6472_);
                    v___x_6483_ = crate::leanh::lean_box(0);
                    v_isShared_6484_ = v_isSharedCheck_6504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6485_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6473_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_6502_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6473_)) as u8;
                if v_isSharedCheck_6502_ == 0 {
                    v_unused_6503_ = crate::leanh::lean_ctor_get(v_traceState_6473_, 0);
                    crate::leanh::lean_dec(v_unused_6503_);
                    v___x_6487_ = v_traceState_6473_;
                    v_isShared_6488_ = v_isSharedCheck_6502_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_traceState_6473_);
                    v___x_6487_ = crate::leanh::lean_box(0);
                    v_isShared_6488_ = v_isSharedCheck_6502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6489_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6489_, 0, v_ref_6436_);
                crate::leanh::lean_ctor_set(v___x_6489_, 1, v_a_6468_);
                v___x_6490_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6434_, v___x_6489_);
                if v_isShared_6488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6487_, 0, v___x_6490_);
                    v___x_6492_ = v___x_6487_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6501_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6501_, 0, v___x_6490_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6501_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6485_,
                    );
                    v___x_6492_ = v_reuseFailAlloc_6501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6483_, 4, v___x_6492_);
                    v___x_6494_ = v___x_6483_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6500_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_env_6474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 1, v_nextMacroScope_6475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 2, v_ngen_6476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 3, v_auxDeclNGen_6477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 4, v___x_6492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 5, v_cache_6478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 6, v_messages_6479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 7, v_infoState_6480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 8, v_snapshotTasks_6481_);
                    v___x_6494_ = v_reuseFailAlloc_6500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6495_ = lean_st_ref_set(v___y_6439_, v___x_6494_);
                v___x_6496_ = crate::leanh::lean_box(0);
                if v_isShared_6471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6470_, 0, v___x_6496_);
                    v___x_6498_ = v___x_6470_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6499_, 0, v___x_6496_);
                    v___x_6498_ = v_reuseFailAlloc_6499_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_oldTraces_6506_: *mut crate::leanh::LeanObject,
    mut v_data_6507_: *mut crate::leanh::LeanObject,
    mut v_ref_6508_: *mut crate::leanh::LeanObject,
    mut v_msg_6509_: *mut crate::leanh::LeanObject,
    mut v___y_6510_: *mut crate::leanh::LeanObject,
    mut v___y_6511_: *mut crate::leanh::LeanObject,
    mut v___y_6512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6513_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_6506_, v_data_6507_, v_ref_6508_, v_msg_6509_, v___y_6510_, v___y_6511_);
    crate::leanh::lean_dec(v___y_6511_);
    crate::leanh::lean_dec_ref(v___y_6510_);
    return v_res_6513_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6515_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__0;
    v___x_6516_ = l_Lean_stringToMessageData(v___x_6515_);
    return v___x_6516_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__2;
    v___x_6519_ = l_Lean_stringToMessageData(v___x_6518_);
    return v___x_6519_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4()
-> f64 {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: f64 = 0.0;
    v___x_6520_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_6521_ = lean_float_of_nat(v___x_6520_);
    return v___x_6521_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(
    mut v_cls_6522_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6523_: u8,
    mut v_tag_6524_: *mut crate::leanh::LeanObject,
    mut v_opts_6525_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6526_: u8,
    mut v_oldTraces_6527_: *mut crate::leanh::LeanObject,
    mut v_msg_6528_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6529_: *mut crate::leanh::LeanObject,
    mut v___y_6530_: *mut crate::leanh::LeanObject,
    mut v___y_6531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___y_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6547_: u8 = 0;
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6551_: u8 = 0;
    let mut v_fst_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: u8 = 0;
    let mut v___y_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_6562_: u8 = 0;
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: f64 = 0.0;
    let mut v_data_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: f64 = 0.0;
    let mut v___x_6576_: f64 = 0.0;
    let mut v_reuseFailAlloc_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6585_: u8 = 0;
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6598_: u8 = 0;
    let mut v_tid_6599_: u64 = 0;
    let mut v_traces_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6603_: u8 = 0;
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut v_isSharedCheck_6614_: u8 = 0;
    let mut v___y_6616_: f64 = 0.0;
    let mut v___x_6617_: f64 = 0.0;
    let mut v___x_6618_: f64 = 0.0;
    let mut v___x_6619_: f64 = 0.0;
    let mut v___x_6620_: u8 = 0;
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: f64 = 0.0;
    let mut v___x_6626_: f64 = 0.0;
    let mut v___x_6627_: f64 = 0.0;
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: f64 = 0.0;
    let mut v_isSharedCheck_6631_: u8 = 0;
    let mut v_isSharedCheck_6632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6533_ = crate::leanh::lean_ctor_get(v_resStartStop_6529_, 0);
                v_snd_6534_ = crate::leanh::lean_ctor_get(v_resStartStop_6529_, 1);
                v_isSharedCheck_6632_ =
                    (!crate::leanh::lean_is_exclusive(v_resStartStop_6529_)) as u8;
                if v_isSharedCheck_6632_ == 0 {
                    v___x_6536_ = v_resStartStop_6529_;
                    v_isShared_6537_ = v_isSharedCheck_6632_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6534_);
                    crate::leanh::lean_inc(v_fst_6533_);
                    crate::leanh::lean_dec(v_resStartStop_6529_);
                    v___x_6536_ = crate::leanh::lean_box(0);
                    v_isShared_6537_ = v_isSharedCheck_6632_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_6552_ = crate::leanh::lean_ctor_get(v_snd_6534_, 0);
                v_snd_6553_ = crate::leanh::lean_ctor_get(v_snd_6534_, 1);
                v_isSharedCheck_6631_ = (!crate::leanh::lean_is_exclusive(v_snd_6534_)) as u8;
                if v_isSharedCheck_6631_ == 0 {
                    v___x_6555_ = v_snd_6534_;
                    v_isShared_6556_ = v_isSharedCheck_6631_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6553_);
                    crate::leanh::lean_inc(v_fst_6552_);
                    crate::leanh::lean_dec(v_snd_6534_);
                    v___x_6555_ = crate::leanh::lean_box(0);
                    v_isShared_6556_ = v_isSharedCheck_6631_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_6540_);
                v___x_6542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__2(v_oldTraces_6527_, v_data_6541_, v___y_6540_, v___y_6539_, v___y_6530_, v___y_6531_);
                if crate::leanh::lean_obj_tag(v___x_6542_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6542_, 1);
                    v___x_6543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_6533_);
                    return v___x_6543_;
                } else {
                    crate::leanh::lean_dec(v_fst_6533_);
                    v_a_6544_ = crate::leanh::lean_ctor_get(v___x_6542_, 0);
                    v_isSharedCheck_6551_ = (!crate::leanh::lean_is_exclusive(v___x_6542_)) as u8;
                    if v_isSharedCheck_6551_ == 0 {
                        v___x_6546_ = v___x_6542_;
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6544_);
                        crate::leanh::lean_dec(v___x_6542_);
                        v___x_6546_ = crate::leanh::lean_box(0);
                        v_isShared_6547_ = v_isSharedCheck_6551_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6547_ == 0 {
                    v___x_6549_ = v___x_6546_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
                    v___x_6549_ = v_reuseFailAlloc_6550_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6549_;
            }
            5 => {
                v___x_6557_ = l_Lean_trace_profiler;
                v___x_6558_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                    v_opts_6525_,
                    v___x_6557_,
                );
                if v___x_6558_ == 0 {
                    v___y_6585_ = v___x_6558_;
                    state = 10;
                    continue;
                } else {
                    v___x_6621_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_6622_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                        v_opts_6525_,
                        v___x_6621_,
                    );
                    if v___x_6622_ == 0 {
                        v___x_6623_ = l_Lean_trace_profiler_threshold;
                        v___x_6624_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(
                            v_opts_6525_,
                            v___x_6623_,
                        );
                        v___x_6625_ = lean_float_of_nat(v___x_6624_);
                        v___x_6626_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__4);
                        v___x_6627_ = lean_float_div(v___x_6625_, v___x_6626_);
                        v___y_6616_ = v___x_6627_;
                        state = 15;
                        continue;
                    } else {
                        v___x_6628_ = l_Lean_trace_profiler_threshold;
                        v___x_6629_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__2(
                            v_opts_6525_,
                            v___x_6628_,
                        );
                        v___x_6630_ = lean_float_of_nat(v___x_6629_);
                        v___y_6616_ = v___x_6630_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_6562_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__1(v_fst_6533_);
                v___x_6563_ = l_Lean_TraceResult_toEmoji(v_result_6562_);
                v___x_6564_ = l_Lean_stringToMessageData(v___x_6563_);
                v___x_6565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__1);
                if v_isShared_6556_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6555_, 7);
                    crate::leanh::lean_ctor_set(v___x_6555_, 1, v___x_6565_);
                    crate::leanh::lean_ctor_set(v___x_6555_, 0, v___x_6564_);
                    v___x_6567_ = v___x_6555_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6578_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6578_, 0, v___x_6564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6578_, 1, v___x_6565_);
                    v___x_6567_ = v_reuseFailAlloc_6578_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6537_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6536_, 7);
                    crate::leanh::lean_ctor_set(v___x_6536_, 1, v_a_6561_);
                    crate::leanh::lean_ctor_set(v___x_6536_, 0, v___x_6567_);
                    v_m_6569_ = v___x_6536_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6577_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6577_, 0, v___x_6567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6577_, 1, v_a_6561_);
                    v_m_6569_ = v_reuseFailAlloc_6577_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6570_ = crate::leanh::lean_box((v_result_6562_) as usize);
                v___x_6571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6571_, 0, v___x_6570_);
                v___x_6572_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__0);
                crate::leanh::lean_inc_ref(v_tag_6524_);
                crate::leanh::lean_inc_ref(v___x_6571_);
                crate::leanh::lean_inc(v_cls_6522_);
                v_data_6573_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v_data_6573_, 0, v_cls_6522_);
                crate::leanh::lean_ctor_set(v_data_6573_, 1, v___x_6571_);
                crate::leanh::lean_ctor_set(v_data_6573_, 2, v_tag_6524_);
                crate::leanh::lean_ctor_set_float(
                    v_data_6573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6572_,
                );
                crate::leanh::lean_ctor_set_float(
                    v_data_6573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6572_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_data_6573_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_6523_,
                );
                if v___x_6558_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6571_, 1);
                    crate::leanh::lean_dec(v_snd_6553_);
                    crate::leanh::lean_dec(v_fst_6552_);
                    crate::leanh::lean_dec_ref(v_tag_6524_);
                    crate::leanh::lean_dec(v_cls_6522_);
                    v___y_6539_ = v_m_6569_;
                    v___y_6540_ = v___y_6560_;
                    v_data_6541_ = v_data_6573_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_data_6573_, 3);
                    v_data_6574_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    crate::leanh::lean_ctor_set(v_data_6574_, 0, v_cls_6522_);
                    crate::leanh::lean_ctor_set(v_data_6574_, 1, v___x_6571_);
                    crate::leanh::lean_ctor_set(v_data_6574_, 2, v_tag_6524_);
                    v___x_6575_ = crate::leanh::lean_unbox_float(v_fst_6552_);
                    crate::leanh::lean_dec(v_fst_6552_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6574_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6575_,
                    );
                    v___x_6576_ = crate::leanh::lean_unbox_float(v_snd_6553_);
                    crate::leanh::lean_dec(v_snd_6553_);
                    crate::leanh::lean_ctor_set_float(
                        v_data_6574_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_6576_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_data_6574_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_6523_,
                    );
                    v___y_6539_ = v_m_6569_;
                    v___y_6540_ = v___y_6560_;
                    v_data_6541_ = v_data_6574_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_6580_ = crate::leanh::lean_ctor_get(v___y_6530_, 5);
                crate::leanh::lean_inc(v___y_6531_);
                crate::leanh::lean_inc_ref(v___y_6530_);
                crate::leanh::lean_inc(v_fst_6533_);
                v___x_6581_ = crate::leanh::lean_apply_4(
                    v_msg_6528_,
                    v_fst_6533_,
                    v___y_6530_,
                    v___y_6531_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6581_) == 0 {
                    v_a_6582_ = crate::leanh::lean_ctor_get(v___x_6581_, 0);
                    crate::leanh::lean_inc(v_a_6582_);
                    crate::leanh::lean_dec_ref_known(v___x_6581_, 1);
                    v___y_6560_ = v_ref_6580_;
                    v_a_6561_ = v_a_6582_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6581_, 1);
                    v___x_6583_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___closed__3);
                    v___y_6560_ = v_ref_6580_;
                    v_a_6561_ = v___x_6583_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_6526_ == 0 {
                    if v___y_6585_ == 0 {
                        crate::leanh::lean_del_object(v___x_6555_);
                        crate::leanh::lean_dec(v_snd_6553_);
                        crate::leanh::lean_dec(v_fst_6552_);
                        crate::leanh::lean_del_object(v___x_6536_);
                        crate::leanh::lean_dec_ref(v_msg_6528_);
                        crate::leanh::lean_dec_ref(v_tag_6524_);
                        crate::leanh::lean_dec(v_cls_6522_);
                        v___x_6586_ = lean_st_ref_take(v___y_6531_);
                        v_traceState_6587_ = crate::leanh::lean_ctor_get(v___x_6586_, 4);
                        v_env_6588_ = crate::leanh::lean_ctor_get(v___x_6586_, 0);
                        v_nextMacroScope_6589_ = crate::leanh::lean_ctor_get(v___x_6586_, 1);
                        v_ngen_6590_ = crate::leanh::lean_ctor_get(v___x_6586_, 2);
                        v_auxDeclNGen_6591_ = crate::leanh::lean_ctor_get(v___x_6586_, 3);
                        v_cache_6592_ = crate::leanh::lean_ctor_get(v___x_6586_, 5);
                        v_messages_6593_ = crate::leanh::lean_ctor_get(v___x_6586_, 6);
                        v_infoState_6594_ = crate::leanh::lean_ctor_get(v___x_6586_, 7);
                        v_snapshotTasks_6595_ = crate::leanh::lean_ctor_get(v___x_6586_, 8);
                        v_isSharedCheck_6614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6586_)) as u8;
                        if v_isSharedCheck_6614_ == 0 {
                            v___x_6597_ = v___x_6586_;
                            v_isShared_6598_ = v_isSharedCheck_6614_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6595_);
                            crate::leanh::lean_inc(v_infoState_6594_);
                            crate::leanh::lean_inc(v_messages_6593_);
                            crate::leanh::lean_inc(v_cache_6592_);
                            crate::leanh::lean_inc(v_traceState_6587_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6591_);
                            crate::leanh::lean_inc(v_ngen_6590_);
                            crate::leanh::lean_inc(v_nextMacroScope_6589_);
                            crate::leanh::lean_inc(v_env_6588_);
                            crate::leanh::lean_dec(v___x_6586_);
                            v___x_6597_ = crate::leanh::lean_box(0);
                            v_isShared_6598_ = v_isSharedCheck_6614_;
                            state = 11;
                            continue;
                        }
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
                v_tid_6599_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6600_ = crate::leanh::lean_ctor_get(v_traceState_6587_, 0);
                v_isSharedCheck_6613_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6587_)) as u8;
                if v_isSharedCheck_6613_ == 0 {
                    v___x_6602_ = v_traceState_6587_;
                    v_isShared_6603_ = v_isSharedCheck_6613_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6600_);
                    crate::leanh::lean_dec(v_traceState_6587_);
                    v___x_6602_ = crate::leanh::lean_box(0);
                    v_isShared_6603_ = v_isSharedCheck_6613_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_6604_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_6527_, v_traces_6600_);
                crate::leanh::lean_dec_ref(v_traces_6600_);
                if v_isShared_6603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6602_, 0, v___x_6604_);
                    v___x_6606_ = v___x_6602_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6612_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6612_, 0, v___x_6604_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6612_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6599_,
                    );
                    v___x_6606_ = v_reuseFailAlloc_6612_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6597_, 4, v___x_6606_);
                    v___x_6608_ = v___x_6597_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6611_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 0, v_env_6588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 1, v_nextMacroScope_6589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 2, v_ngen_6590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 3, v_auxDeclNGen_6591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 4, v___x_6606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 5, v_cache_6592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 6, v_messages_6593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 7, v_infoState_6594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6611_, 8, v_snapshotTasks_6595_);
                    v___x_6608_ = v_reuseFailAlloc_6611_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6609_ = lean_st_ref_set(v___y_6531_, v___x_6608_);
                v___x_6610_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_fst_6533_);
                return v___x_6610_;
            }
            15 => {
                v___x_6617_ = crate::leanh::lean_unbox_float(v_snd_6553_);
                v___x_6618_ = crate::leanh::lean_unbox_float(v_fst_6552_);
                v___x_6619_ = lean_float_sub(v___x_6617_, v___x_6618_);
                v___x_6620_ = lean_float_decLt(v___y_6616_, v___x_6619_);
                v___y_6585_ = v___x_6620_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1___boxed(
    mut v_cls_6633_: *mut crate::leanh::LeanObject,
    mut v_collapsed_6634_: *mut crate::leanh::LeanObject,
    mut v_tag_6635_: *mut crate::leanh::LeanObject,
    mut v_opts_6636_: *mut crate::leanh::LeanObject,
    mut v_clsEnabled_6637_: *mut crate::leanh::LeanObject,
    mut v_oldTraces_6638_: *mut crate::leanh::LeanObject,
    mut v_msg_6639_: *mut crate::leanh::LeanObject,
    mut v_resStartStop_6640_: *mut crate::leanh::LeanObject,
    mut v___y_6641_: *mut crate::leanh::LeanObject,
    mut v___y_6642_: *mut crate::leanh::LeanObject,
    mut v___y_6643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_collapsed_boxed_6644_: u8 = 0;
    let mut v_clsEnabled_boxed_6645_: u8 = 0;
    let mut v_res_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_6644_ = (crate::leanh::lean_unbox(v_collapsed_6634_) as u8);
    v_clsEnabled_boxed_6645_ = (crate::leanh::lean_unbox(v_clsEnabled_6637_) as u8);
    v_res_6646_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v_cls_6633_, v_collapsed_boxed_6644_, v_tag_6635_, v_opts_6636_, v_clsEnabled_boxed_6645_, v_oldTraces_6638_, v_msg_6639_, v_resStartStop_6640_, v___y_6641_, v___y_6642_);
    crate::leanh::lean_dec(v___y_6642_);
    crate::leanh::lean_dec_ref(v___y_6641_);
    crate::leanh::lean_dec_ref(v_opts_6636_);
    return v_res_6646_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6649_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1,
    );
    v___x_6650_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6651_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6651_, 0, v___x_6650_);
    crate::leanh::lean_ctor_set(v___x_6651_, 1, v___x_6650_);
    crate::leanh::lean_ctor_set(v___x_6651_, 2, v___x_6650_);
    crate::leanh::lean_ctor_set(v___x_6651_, 3, v___x_6650_);
    crate::leanh::lean_ctor_set(v___x_6651_, 4, v___x_6649_);
    crate::leanh::lean_ctor_set(v___x_6651_, 5, v___x_6649_);
    crate::leanh::lean_ctor_set(v___x_6651_, 6, v___x_6649_);
    crate::leanh::lean_ctor_set(v___x_6651_, 7, v___x_6649_);
    crate::leanh::lean_ctor_set(v___x_6651_, 8, v___x_6649_);
    crate::leanh::lean_ctor_set(v___x_6651_, 9, v___x_6649_);
    return v___x_6651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6652_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1,
    );
    v___x_6653_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6653_, 0, v___x_6652_);
    crate::leanh::lean_ctor_set(v___x_6653_, 1, v___x_6652_);
    crate::leanh::lean_ctor_set(v___x_6653_, 2, v___x_6652_);
    crate::leanh::lean_ctor_set(v___x_6653_, 3, v___x_6652_);
    crate::leanh::lean_ctor_set(v___x_6653_, 4, v___x_6652_);
    crate::leanh::lean_ctor_set(v___x_6653_, 5, v___x_6652_);
    return v___x_6653_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6654_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1_once
        ),
        _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1,
    );
    v___x_6655_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6655_, 0, v___x_6654_);
    crate::leanh::lean_ctor_set(v___x_6655_, 1, v___x_6654_);
    crate::leanh::lean_ctor_set(v___x_6655_, 2, v___x_6654_);
    crate::leanh::lean_ctor_set(v___x_6655_, 3, v___x_6654_);
    crate::leanh::lean_ctor_set(v___x_6655_, 4, v___x_6654_);
    return v___x_6655_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6656_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_6657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwReservedNameNotAvailable___at___00Lean_ensureReservedNameAvailable___at___00Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0_spec__1_spec__2___closed__4);
    v___x_6658_ = crate::leanh::lean_box(1);
    v___x_6659_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_6660_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_6661_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6661_, 0, v___x_6660_);
    crate::leanh::lean_ctor_set(v___x_6661_, 1, v___x_6659_);
    crate::leanh::lean_ctor_set(v___x_6661_, 2, v___x_6658_);
    crate::leanh::lean_ctor_set(v___x_6661_, 3, v___x_6657_);
    crate::leanh::lean_ctor_set(v___x_6661_, 4, v___x_6656_);
    return v___x_6661_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6665_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_6666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_withEqnOptions_spec__3___closed__1;
    v___x_6667_ = l_Lean_Name_append(v___x_6666_, v___x_6665_);
    return v___x_6667_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> f64 {
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: f64 = 0.0;
    v___x_6668_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_6669_ = lean_float_of_nat(v___x_6668_);
    return v___x_6669_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(
    mut v___f_6670_: *mut crate::leanh::LeanObject,
    mut v_name_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
    mut v___y_6673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6676_: u8 = 0;
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6683_: u8 = 0;
    let mut v_fst_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: u8 = 0;
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: u8 = 0;
    let mut v_a_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6703_: u8 = 0;
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6708_: u8 = 0;
    let mut v_unused_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: u8 = 0;
    let mut v_a_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6723_: u8 = 0;
    let mut v_unused_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: u8 = 0;
    let mut v___x_6728_: u8 = 0;
    let mut v___x_6729_: u8 = 0;
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: u64 = 0;
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6748_: u8 = 0;
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6752_: u8 = 0;
    let mut v___x_6753_: u8 = 0;
    let mut v___x_6754_: u8 = 0;
    let mut v___x_6755_: u8 = 0;
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: u64 = 0;
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6774_: u8 = 0;
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6778_: u8 = 0;
    let mut v_isSharedCheck_6779_: u8 = 0;
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: u8 = 0;
    let mut v___y_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: f64 = 0.0;
    let mut v___x_6794_: f64 = 0.0;
    let mut v___x_6795_: f64 = 0.0;
    let mut v___x_6796_: f64 = 0.0;
    let mut v___x_6797_: f64 = 0.0;
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6806_: u8 = 0;
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6810_: u8 = 0;
    let mut v___y_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6815_: u8 = 0;
    let mut v___y_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: f64 = 0.0;
    let mut v___x_6830_: f64 = 0.0;
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6839_: u8 = 0;
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6844_: u8 = 0;
    let mut v___y_6845_: u8 = 0;
    let mut v___y_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6850_: u8 = 0;
    let mut v___y_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: u8 = 0;
    let mut v___y_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: u8 = 0;
    let mut v_a_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: u8 = 0;
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: u8 = 0;
    let mut v___x_6882_: u8 = 0;
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: u8 = 0;
    let mut v___x_6885_: u8 = 0;
    let mut v___x_6886_: u8 = 0;
    let mut v___x_6887_: u8 = 0;
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: u64 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: u8 = 0;
    let mut v___x_6906_: u8 = 0;
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: u64 = 0;
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: u8 = 0;
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: u8 = 0;
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: u8 = 0;
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: u8 = 0;
    let mut v___x_6942_: u8 = 0;
    let mut v___x_6943_: u8 = 0;
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: u64 = 0;
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: u8 = 0;
    let mut v___x_6961_: u8 = 0;
    let mut v___x_6962_: u8 = 0;
    let mut v___x_6963_: u8 = 0;
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: u64 = 0;
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: u8 = 0;
    let mut v_a_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6990_: u8 = 0;
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6995_: u8 = 0;
    let mut v_unused_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7008_: u8 = 0;
    let mut v_unused_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7016_: u8 = 0;
    let mut v_fst_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: u8 = 0;
    let mut v___x_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: u8 = 0;
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: u8 = 0;
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: u8 = 0;
    let mut v___x_7035_: u8 = 0;
    let mut v___x_7036_: u8 = 0;
    let mut v___x_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: u64 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7055_: u8 = 0;
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7059_: u8 = 0;
    let mut v___x_7060_: u8 = 0;
    let mut v___x_7061_: u8 = 0;
    let mut v___x_7062_: u8 = 0;
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: u64 = 0;
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7081_: u8 = 0;
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7085_: u8 = 0;
    let mut v_isSharedCheck_7086_: u8 = 0;
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6675_ = crate::leanh::lean_ctor_get(v___y_6672_, 2);
                v_hasTrace_6676_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6675_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_6676_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_6670_);
                    v___x_6677_ = lean_st_ref_get(v___y_6673_);
                    v_env_6678_ = crate::leanh::lean_ctor_get(v___x_6677_, 0);
                    crate::leanh::lean_inc_ref(v_env_6678_);
                    crate::leanh::lean_dec(v___x_6677_);
                    crate::leanh::lean_inc(v_name_6671_);
                    v___x_6679_ = l_Lean_Meta_declFromEqLikeName(v_env_6678_, v_name_6671_);
                    if crate::leanh::lean_obj_tag(v___x_6679_) == 1 {
                        v_val_6680_ = crate::leanh::lean_ctor_get(v___x_6679_, 0);
                        v_isSharedCheck_6779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6679_)) as u8;
                        if v_isSharedCheck_6779_ == 0 {
                            v___x_6682_ = v___x_6679_;
                            v_isShared_6683_ = v_isSharedCheck_6779_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6680_);
                            crate::leanh::lean_dec(v___x_6679_);
                            v___x_6682_ = crate::leanh::lean_box(0);
                            v_isShared_6683_ = v_isSharedCheck_6779_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6679_);
                        crate::leanh::lean_dec(v_name_6671_);
                        v___x_6780_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                        v___x_6781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6781_, 0, v___x_6780_);
                        return v___x_6781_;
                    }
                } else {
                    v_inheritedTraceOptions_6782_ = crate::leanh::lean_ctor_get(v___y_6672_, 13);
                    crate::leanh::lean_inc(v_name_6671_);
                    v___f_6783_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 1);
                    crate::leanh::lean_closure_set(v___f_6783_, 0, v_name_6671_);
                    v___x_6784_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                    v___x_6785_ = l_Lean_addTrace___at___00Lean_Meta_saveEqnAffectingOptions_spec__1___closed__1;
                    v___x_6786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__7_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                    v___x_6787_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6782_,
                        v_options_6675_,
                        v___x_6786_,
                    );
                    if v___x_6787_ == 0 {
                        v___x_6982_ = l_Lean_trace_profiler;
                        v___x_6983_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                            v_options_6675_,
                            v___x_6982_,
                        );
                        if v___x_6983_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_6783_);
                            crate::leanh::lean_dec_ref(v___f_6670_);
                            v___x_7010_ = lean_st_ref_get(v___y_6673_);
                            v_env_7011_ = crate::leanh::lean_ctor_get(v___x_7010_, 0);
                            crate::leanh::lean_inc_ref(v_env_7011_);
                            crate::leanh::lean_dec(v___x_7010_);
                            crate::leanh::lean_inc(v_name_6671_);
                            v___x_7012_ = l_Lean_Meta_declFromEqLikeName(v_env_7011_, v_name_6671_);
                            if crate::leanh::lean_obj_tag(v___x_7012_) == 1 {
                                v_val_7013_ = crate::leanh::lean_ctor_get(v___x_7012_, 0);
                                v_isSharedCheck_7086_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7012_)) as u8;
                                if v_isSharedCheck_7086_ == 0 {
                                    v___x_7015_ = v___x_7012_;
                                    v_isShared_7016_ = v_isSharedCheck_7086_;
                                    state = 32;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_7013_);
                                    crate::leanh::lean_dec(v___x_7012_);
                                    v___x_7015_ = crate::leanh::lean_box(0);
                                    v_isShared_7016_ = v_isSharedCheck_7086_;
                                    state = 32;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_7012_);
                                crate::leanh::lean_dec(v_name_6671_);
                                v___x_7087_ = crate::leanh::lean_box((v___x_6983_) as usize);
                                v___x_7088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7088_, 0, v___x_7087_);
                                return v___x_7088_;
                            }
                        } else {
                            state = 25;
                            continue;
                        }
                    } else {
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6684_ = crate::leanh::lean_ctor_get(v_val_6680_, 0);
                crate::leanh::lean_inc_n(v_fst_6684_, 2);
                v_snd_6685_ = crate::leanh::lean_ctor_get(v_val_6680_, 1);
                crate::leanh::lean_inc_n(v_snd_6685_, 2);
                crate::leanh::lean_dec(v_val_6680_);
                v___x_6686_ = lean_st_ref_get(v___y_6673_);
                v_env_6687_ = crate::leanh::lean_ctor_get(v___x_6686_, 0);
                crate::leanh::lean_inc_ref(v_env_6687_);
                crate::leanh::lean_dec(v___x_6686_);
                v___x_6688_ = l_Lean_Meta_mkEqLikeNameFor(v_env_6687_, v_fst_6684_, v_snd_6685_);
                v___x_6689_ = lean_name_eq(v_name_6671_, v___x_6688_);
                crate::leanh::lean_dec(v___x_6688_);
                crate::leanh::lean_dec(v_name_6671_);
                if v___x_6689_ == 0 {
                    crate::leanh::lean_dec(v_snd_6685_);
                    crate::leanh::lean_dec(v_fst_6684_);
                    v___x_6690_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                    if v_isShared_6683_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6682_, 0);
                        crate::leanh::lean_ctor_set(v___x_6682_, 0, v___x_6690_);
                        v___x_6692_ = v___x_6682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6693_, 0, v___x_6690_);
                        v___x_6692_ = v_reuseFailAlloc_6693_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_snd_6685_);
                    v___x_6694_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_6685_);
                    if v___x_6694_ == 0 {
                        crate::leanh::lean_del_object(v___x_6682_);
                        v___x_6710_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                        v___x_6711_ = lean_string_dec_eq(v_snd_6685_, v___x_6710_);
                        crate::leanh::lean_dec(v_snd_6685_);
                        if v___x_6711_ == 0 {
                            crate::leanh::lean_dec(v_fst_6684_);
                            v___x_6725_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                            v___x_6726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6726_, 0, v___x_6725_);
                            return v___x_6726_;
                        } else {
                            v___x_6727_ = 1;
                            v___x_6728_ = 0;
                            v___x_6729_ = 2;
                            v___x_6730_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                0 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                1 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                2 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                3 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                4 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 5 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 6 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6730_,
                                7 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 8 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 9 as u32, v___x_6727_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 10 as u32, v___x_6728_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 11 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 12 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 13 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 14 as u32, v___x_6729_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 15 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 16 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 17 as u32, v___x_6711_);
                            crate::leanh::lean_ctor_set_uint8(v___x_6730_, 18 as u32, v___x_6711_);
                            v___x_6731_ =
                                l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6730_);
                            v___x_6732_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                            crate::leanh::lean_ctor_set(v___x_6732_, 0, v___x_6730_);
                            crate::leanh::lean_ctor_set_uint64(
                                v___x_6732_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_6731_,
                            );
                            v___x_6733_ = crate::leanh::lean_box(1);
                            v___x_6734_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_6735_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                            v___x_6736_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                            v___x_6737_ = crate::leanh::lean_box(0);
                            v___x_6738_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                            crate::leanh::lean_ctor_set(v___x_6738_, 0, v___x_6732_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 1, v___x_6733_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 2, v___x_6735_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 3, v___x_6736_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 4, v___x_6737_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 5, v___x_6734_);
                            crate::leanh::lean_ctor_set(v___x_6738_, 6, v___x_6737_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6738_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6738_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1)
                                    as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6738_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2)
                                    as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_6738_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3)
                                    as u32,
                                v___x_6689_,
                            );
                            v___x_6739_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                            v___x_6740_ = lean_st_mk_ref(v___x_6739_);
                            v___x_6741_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                                v_fst_6684_,
                                v___x_6689_,
                                v___x_6738_,
                                v___x_6740_,
                                v___y_6672_,
                                v___y_6673_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_6738_, 7);
                            if crate::leanh::lean_obj_tag(v___x_6741_) == 0 {
                                v_a_6742_ = crate::leanh::lean_ctor_get(v___x_6741_, 0);
                                crate::leanh::lean_inc(v_a_6742_);
                                crate::leanh::lean_dec_ref_known(v___x_6741_, 1);
                                v___x_6743_ = lean_st_ref_get(v___x_6740_);
                                crate::leanh::lean_dec(v___x_6740_);
                                crate::leanh::lean_dec(v___x_6743_);
                                v_a_6713_ = v_a_6742_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6740_);
                                if crate::leanh::lean_obj_tag(v___x_6741_) == 0 {
                                    v_a_6744_ = crate::leanh::lean_ctor_get(v___x_6741_, 0);
                                    crate::leanh::lean_inc(v_a_6744_);
                                    crate::leanh::lean_dec_ref_known(v___x_6741_, 1);
                                    v_a_6713_ = v_a_6744_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_a_6745_ = crate::leanh::lean_ctor_get(v___x_6741_, 0);
                                    v_isSharedCheck_6752_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6741_)) as u8;
                                    if v_isSharedCheck_6752_ == 0 {
                                        v___x_6747_ = v___x_6741_;
                                        v_isShared_6748_ = v_isSharedCheck_6752_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6745_);
                                        crate::leanh::lean_dec(v___x_6741_);
                                        v___x_6747_ = crate::leanh::lean_box(0);
                                        v_isShared_6748_ = v_isSharedCheck_6752_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_6685_);
                        v___x_6753_ = 1;
                        v___x_6754_ = 0;
                        v___x_6755_ = 2;
                        v___x_6756_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 0 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 1 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 2 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 3 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 4 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 5 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 6 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 7 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 8 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 9 as u32, v___x_6753_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 10 as u32, v___x_6754_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 11 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 12 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 13 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 14 as u32, v___x_6755_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 15 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 16 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 17 as u32, v___x_6694_);
                        crate::leanh::lean_ctor_set_uint8(v___x_6756_, 18 as u32, v___x_6694_);
                        v___x_6757_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6756_);
                        v___x_6758_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        crate::leanh::lean_ctor_set(v___x_6758_, 0, v___x_6756_);
                        crate::leanh::lean_ctor_set_uint64(
                            v___x_6758_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6757_,
                        );
                        v___x_6759_ = crate::leanh::lean_box(1);
                        v___x_6760_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                        v___x_6762_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                        v___x_6763_ = crate::leanh::lean_box(0);
                        v___x_6764_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                        crate::leanh::lean_ctor_set(v___x_6764_, 0, v___x_6758_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 1, v___x_6759_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 2, v___x_6761_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 3, v___x_6762_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 4, v___x_6763_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 5, v___x_6760_);
                        crate::leanh::lean_ctor_set(v___x_6764_, 6, v___x_6763_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6764_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                            v_hasTrace_6676_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6764_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                            v_hasTrace_6676_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6764_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                            v_hasTrace_6676_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6764_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                            v___x_6689_,
                        );
                        v___x_6765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                        v___x_6766_ = lean_st_mk_ref(v___x_6765_);
                        v___x_6767_ = l_Lean_Meta_getEqnsFor_x3f(
                            v_fst_6684_,
                            v___x_6764_,
                            v___x_6766_,
                            v___y_6672_,
                            v___y_6673_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_6764_, 7);
                        if crate::leanh::lean_obj_tag(v___x_6767_) == 0 {
                            v_a_6768_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                            crate::leanh::lean_inc(v_a_6768_);
                            crate::leanh::lean_dec_ref_known(v___x_6767_, 1);
                            v___x_6769_ = lean_st_ref_get(v___x_6766_);
                            crate::leanh::lean_dec(v___x_6766_);
                            crate::leanh::lean_dec(v___x_6769_);
                            v_a_6696_ = v_a_6768_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6766_);
                            if crate::leanh::lean_obj_tag(v___x_6767_) == 0 {
                                v_a_6770_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                                crate::leanh::lean_inc(v_a_6770_);
                                crate::leanh::lean_dec_ref_known(v___x_6767_, 1);
                                v_a_6696_ = v_a_6770_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_6682_);
                                v_a_6771_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                                v_isSharedCheck_6778_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6767_)) as u8;
                                if v_isSharedCheck_6778_ == 0 {
                                    v___x_6773_ = v___x_6767_;
                                    v_isShared_6774_ = v_isSharedCheck_6778_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6771_);
                                    crate::leanh::lean_dec(v___x_6767_);
                                    v___x_6773_ = crate::leanh::lean_box(0);
                                    v_isShared_6774_ = v_isSharedCheck_6778_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_6692_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_6696_) == 0 {
                    v___x_6697_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                    if v_isShared_6683_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6682_, 0);
                        crate::leanh::lean_ctor_set(v___x_6682_, 0, v___x_6697_);
                        v___x_6699_ = v___x_6682_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6700_, 0, v___x_6697_);
                        v___x_6699_ = v_reuseFailAlloc_6700_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6682_);
                    v_isSharedCheck_6708_ = (!crate::leanh::lean_is_exclusive(v_a_6696_)) as u8;
                    if v_isSharedCheck_6708_ == 0 {
                        v_unused_6709_ = crate::leanh::lean_ctor_get(v_a_6696_, 0);
                        crate::leanh::lean_dec(v_unused_6709_);
                        v___x_6702_ = v_a_6696_;
                        v_isShared_6703_ = v_isSharedCheck_6708_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6696_);
                        v___x_6702_ = crate::leanh::lean_box(0);
                        v_isShared_6703_ = v_isSharedCheck_6708_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6699_;
            }
            5 => {
                v___x_6704_ = crate::leanh::lean_box((v___x_6694_) as usize);
                if v_isShared_6703_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6702_, 0);
                    crate::leanh::lean_ctor_set(v___x_6702_, 0, v___x_6704_);
                    v___x_6706_ = v___x_6702_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6707_, 0, v___x_6704_);
                    v___x_6706_ = v_reuseFailAlloc_6707_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6706_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_6713_) == 0 {
                    v___x_6714_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                    v___x_6715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6715_, 0, v___x_6714_);
                    return v___x_6715_;
                } else {
                    v_isSharedCheck_6723_ = (!crate::leanh::lean_is_exclusive(v_a_6713_)) as u8;
                    if v_isSharedCheck_6723_ == 0 {
                        v_unused_6724_ = crate::leanh::lean_ctor_get(v_a_6713_, 0);
                        crate::leanh::lean_dec(v_unused_6724_);
                        v___x_6717_ = v_a_6713_;
                        v_isShared_6718_ = v_isSharedCheck_6723_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6713_);
                        v___x_6717_ = crate::leanh::lean_box(0);
                        v_isShared_6718_ = v_isSharedCheck_6723_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6719_ = crate::leanh::lean_box((v___x_6711_) as usize);
                if v_isShared_6718_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6717_, 0);
                    crate::leanh::lean_ctor_set(v___x_6717_, 0, v___x_6719_);
                    v___x_6721_ = v___x_6717_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6722_, 0, v___x_6719_);
                    v___x_6721_ = v_reuseFailAlloc_6722_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6721_;
            }
            10 => {
                if v_isShared_6748_ == 0 {
                    v___x_6750_ = v___x_6747_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_a_6745_);
                    v___x_6750_ = v_reuseFailAlloc_6751_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6750_;
            }
            12 => {
                if v_isShared_6774_ == 0 {
                    v___x_6776_ = v___x_6773_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6777_, 0, v_a_6771_);
                    v___x_6776_ = v_reuseFailAlloc_6777_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6776_;
            }
            14 => {
                v___x_6792_ = lean_io_mono_nanos_now();
                v___x_6793_ = lean_float_of_nat(v___y_6789_);
                v___x_6794_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__8_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                v___x_6795_ = lean_float_div(v___x_6793_, v___x_6794_);
                v___x_6796_ = lean_float_of_nat(v___x_6792_);
                v___x_6797_ = lean_float_div(v___x_6796_, v___x_6794_);
                v___x_6798_ = crate::leanh::lean_box_float(v___x_6795_);
                v___x_6799_ = crate::leanh::lean_box_float(v___x_6797_);
                v___x_6800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6800_, 0, v___x_6798_);
                crate::leanh::lean_ctor_set(v___x_6800_, 1, v___x_6799_);
                v___x_6801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6801_, 0, v_a_6791_);
                crate::leanh::lean_ctor_set(v___x_6801_, 1, v___x_6800_);
                v___x_6802_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_6784_, v_hasTrace_6676_, v___x_6785_, v_options_6675_, v___x_6787_, v___y_6790_, v___f_6783_, v___x_6801_, v___y_6672_, v___y_6673_);
                return v___x_6802_;
            }
            15 => {
                v___x_6807_ = crate::leanh::lean_box((v_a_6806_) as usize);
                v___x_6808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6808_, 0, v___x_6807_);
                v___y_6789_ = v___y_6804_;
                v___y_6790_ = v___y_6805_;
                v_a_6791_ = v___x_6808_;
                state = 14;
                continue;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_a_6813_) == 0 {
                    v___y_6804_ = v___y_6811_;
                    v___y_6805_ = v___y_6812_;
                    v_a_6806_ = v___y_6810_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6813_, 1);
                    v___y_6804_ = v___y_6811_;
                    v___y_6805_ = v___y_6812_;
                    v_a_6806_ = v_hasTrace_6676_;
                    state = 15;
                    continue;
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_6818_) == 0 {
                    v___y_6804_ = v___y_6816_;
                    v___y_6805_ = v___y_6817_;
                    v_a_6806_ = v___y_6815_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6818_, 1);
                    v___y_6804_ = v___y_6816_;
                    v___y_6805_ = v___y_6817_;
                    v_a_6806_ = v_hasTrace_6676_;
                    state = 15;
                    continue;
                }
            }
            18 => {
                v___x_6823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6823_, 0, v_a_6822_);
                v___y_6789_ = v___y_6820_;
                v___y_6790_ = v___y_6821_;
                v_a_6791_ = v___x_6823_;
                state = 14;
                continue;
            }
            19 => {
                v___x_6828_ = lean_io_get_num_heartbeats();
                v___x_6829_ = lean_float_of_nat(v___y_6825_);
                v___x_6830_ = lean_float_of_nat(v___x_6828_);
                v___x_6831_ = crate::leanh::lean_box_float(v___x_6829_);
                v___x_6832_ = crate::leanh::lean_box_float(v___x_6830_);
                v___x_6833_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6833_, 0, v___x_6831_);
                crate::leanh::lean_ctor_set(v___x_6833_, 1, v___x_6832_);
                v___x_6834_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6834_, 0, v_a_6827_);
                crate::leanh::lean_ctor_set(v___x_6834_, 1, v___x_6833_);
                v___x_6835_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1(v___x_6784_, v_hasTrace_6676_, v___x_6785_, v_options_6675_, v___x_6787_, v___y_6826_, v___f_6783_, v___x_6834_, v___y_6672_, v___y_6673_);
                return v___x_6835_;
            }
            20 => {
                v___x_6840_ = crate::leanh::lean_box((v_a_6839_) as usize);
                v___x_6841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6841_, 0, v___x_6840_);
                v___y_6825_ = v___y_6837_;
                v___y_6826_ = v___y_6838_;
                v_a_6827_ = v___x_6841_;
                state = 19;
                continue;
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_a_6847_) == 0 {
                    v___y_6837_ = v___y_6843_;
                    v___y_6838_ = v___y_6846_;
                    v_a_6839_ = v___y_6845_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6847_, 1);
                    v___y_6837_ = v___y_6843_;
                    v___y_6838_ = v___y_6846_;
                    v_a_6839_ = v___y_6844_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                if crate::leanh::lean_obj_tag(v_a_6852_) == 0 {
                    v___x_6853_ = 0;
                    v___y_6837_ = v___y_6849_;
                    v___y_6838_ = v___y_6851_;
                    v_a_6839_ = v___x_6853_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_6852_, 1);
                    v___y_6837_ = v___y_6849_;
                    v___y_6838_ = v___y_6851_;
                    v_a_6839_ = v___y_6850_;
                    state = 20;
                    continue;
                }
            }
            23 => {
                v___x_6858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6858_, 0, v_a_6857_);
                v___y_6825_ = v___y_6855_;
                v___y_6826_ = v___y_6856_;
                v_a_6827_ = v___x_6858_;
                state = 19;
                continue;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_6862_) == 0 {
                    v_a_6863_ = crate::leanh::lean_ctor_get(v___y_6862_, 0);
                    crate::leanh::lean_inc(v_a_6863_);
                    crate::leanh::lean_dec_ref_known(v___y_6862_, 1);
                    v___x_6864_ = (crate::leanh::lean_unbox(v_a_6863_) as u8);
                    crate::leanh::lean_dec(v_a_6863_);
                    v___y_6837_ = v___y_6860_;
                    v___y_6838_ = v___y_6861_;
                    v_a_6839_ = v___x_6864_;
                    state = 20;
                    continue;
                } else {
                    v_a_6865_ = crate::leanh::lean_ctor_get(v___y_6862_, 0);
                    crate::leanh::lean_inc(v_a_6865_);
                    crate::leanh::lean_dec_ref_known(v___y_6862_, 1);
                    v___y_6855_ = v___y_6860_;
                    v___y_6856_ = v___y_6861_;
                    v_a_6857_ = v_a_6865_;
                    state = 23;
                    continue;
                }
            }
            25 => {
                v___x_6867_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__0___redArg(v___y_6673_);
                v_a_6868_ = crate::leanh::lean_ctor_get(v___x_6867_, 0);
                crate::leanh::lean_inc(v_a_6868_);
                crate::leanh::lean_dec_ref(v___x_6867_);
                v___x_6869_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_6870_ = l_Lean_Option_get___at___00Lean_Meta_withEqnOptions_spec__1(
                    v_options_6675_,
                    v___x_6869_,
                );
                if v___x_6870_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_6670_);
                    v___x_6871_ = lean_io_mono_nanos_now();
                    v___x_6872_ = lean_st_ref_get(v___y_6673_);
                    v_env_6873_ = crate::leanh::lean_ctor_get(v___x_6872_, 0);
                    crate::leanh::lean_inc_ref(v_env_6873_);
                    crate::leanh::lean_dec(v___x_6872_);
                    crate::leanh::lean_inc(v_name_6671_);
                    v___x_6874_ = l_Lean_Meta_declFromEqLikeName(v_env_6873_, v_name_6671_);
                    if crate::leanh::lean_obj_tag(v___x_6874_) == 1 {
                        v_val_6875_ = crate::leanh::lean_ctor_get(v___x_6874_, 0);
                        crate::leanh::lean_inc(v_val_6875_);
                        crate::leanh::lean_dec_ref_known(v___x_6874_, 1);
                        v_fst_6876_ = crate::leanh::lean_ctor_get(v_val_6875_, 0);
                        crate::leanh::lean_inc_n(v_fst_6876_, 2);
                        v_snd_6877_ = crate::leanh::lean_ctor_get(v_val_6875_, 1);
                        crate::leanh::lean_inc_n(v_snd_6877_, 2);
                        crate::leanh::lean_dec(v_val_6875_);
                        v___x_6878_ = lean_st_ref_get(v___y_6673_);
                        v_env_6879_ = crate::leanh::lean_ctor_get(v___x_6878_, 0);
                        crate::leanh::lean_inc_ref(v_env_6879_);
                        crate::leanh::lean_dec(v___x_6878_);
                        v___x_6880_ =
                            l_Lean_Meta_mkEqLikeNameFor(v_env_6879_, v_fst_6876_, v_snd_6877_);
                        v___x_6881_ = lean_name_eq(v_name_6671_, v___x_6880_);
                        crate::leanh::lean_dec(v___x_6880_);
                        crate::leanh::lean_dec(v_name_6671_);
                        if v___x_6881_ == 0 {
                            crate::leanh::lean_dec(v_snd_6877_);
                            crate::leanh::lean_dec(v_fst_6876_);
                            v___y_6804_ = v___x_6871_;
                            v___y_6805_ = v_a_6868_;
                            v_a_6806_ = v___x_6870_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_6877_);
                            v___x_6882_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_6877_);
                            if v___x_6882_ == 0 {
                                v___x_6883_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                                v___x_6884_ = lean_string_dec_eq(v_snd_6877_, v___x_6883_);
                                crate::leanh::lean_dec(v_snd_6877_);
                                if v___x_6884_ == 0 {
                                    crate::leanh::lean_dec(v_fst_6876_);
                                    v___y_6804_ = v___x_6871_;
                                    v___y_6805_ = v_a_6868_;
                                    v_a_6806_ = v___x_6870_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_6885_ = 1;
                                    v___x_6886_ = 0;
                                    v___x_6887_ = 2;
                                    v___x_6888_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        0 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        1 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        2 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        3 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        4 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        5 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        6 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        7 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        8 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        9 as u32,
                                        v___x_6885_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        10 as u32,
                                        v___x_6886_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        11 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        12 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        13 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        14 as u32,
                                        v___x_6887_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        15 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        16 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        17 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6888_,
                                        18 as u32,
                                        v_hasTrace_6676_,
                                    );
                                    v___x_6889_ =
                                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                            v___x_6888_,
                                        );
                                    v___x_6890_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6890_, 0, v___x_6888_);
                                    crate::leanh::lean_ctor_set_uint64(
                                        v___x_6890_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_6889_,
                                    );
                                    v___x_6891_ = crate::leanh::lean_box(1);
                                    v___x_6892_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_6893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                                    v___x_6894_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                                    v___x_6895_ = crate::leanh::lean_box(0);
                                    v___x_6896_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 0, v___x_6890_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 1, v___x_6891_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 2, v___x_6893_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 3, v___x_6894_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 4, v___x_6895_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 5, v___x_6892_);
                                    crate::leanh::lean_ctor_set(v___x_6896_, 6, v___x_6895_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6896_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7)
                                            as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6896_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 1) as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6896_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 2) as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6896_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 3) as u32,
                                        v_hasTrace_6676_,
                                    );
                                    v___x_6897_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                                    v___x_6898_ = lean_st_mk_ref(v___x_6897_);
                                    v___x_6899_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                                        v_fst_6876_,
                                        v_hasTrace_6676_,
                                        v___x_6896_,
                                        v___x_6898_,
                                        v___y_6672_,
                                        v___y_6673_,
                                    );
                                    crate::leanh::lean_dec_ref_known(v___x_6896_, 7);
                                    if crate::leanh::lean_obj_tag(v___x_6899_) == 0 {
                                        v_a_6900_ = crate::leanh::lean_ctor_get(v___x_6899_, 0);
                                        crate::leanh::lean_inc(v_a_6900_);
                                        crate::leanh::lean_dec_ref_known(v___x_6899_, 1);
                                        v___x_6901_ = lean_st_ref_get(v___x_6898_);
                                        crate::leanh::lean_dec(v___x_6898_);
                                        crate::leanh::lean_dec(v___x_6901_);
                                        v___y_6815_ = v___x_6870_;
                                        v___y_6816_ = v___x_6871_;
                                        v___y_6817_ = v_a_6868_;
                                        v_a_6818_ = v_a_6900_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6898_);
                                        if crate::leanh::lean_obj_tag(v___x_6899_) == 0 {
                                            v_a_6902_ = crate::leanh::lean_ctor_get(v___x_6899_, 0);
                                            crate::leanh::lean_inc(v_a_6902_);
                                            crate::leanh::lean_dec_ref_known(v___x_6899_, 1);
                                            v___y_6815_ = v___x_6870_;
                                            v___y_6816_ = v___x_6871_;
                                            v___y_6817_ = v_a_6868_;
                                            v_a_6818_ = v_a_6902_;
                                            state = 17;
                                            continue;
                                        } else {
                                            v_a_6903_ = crate::leanh::lean_ctor_get(v___x_6899_, 0);
                                            crate::leanh::lean_inc(v_a_6903_);
                                            crate::leanh::lean_dec_ref_known(v___x_6899_, 1);
                                            v___y_6820_ = v___x_6871_;
                                            v___y_6821_ = v_a_6868_;
                                            v_a_6822_ = v_a_6903_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_6877_);
                                v___x_6904_ = 1;
                                v___x_6905_ = 0;
                                v___x_6906_ = 2;
                                v___x_6907_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    0 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    1 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    2 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    3 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    4 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    5 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    6 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    7 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    8 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    9 as u32,
                                    v___x_6904_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    10 as u32,
                                    v___x_6905_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    11 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    12 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    13 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    14 as u32,
                                    v___x_6906_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    15 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    16 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    17 as u32,
                                    v_hasTrace_6676_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6907_,
                                    18 as u32,
                                    v_hasTrace_6676_,
                                );
                                v___x_6908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                    v___x_6907_,
                                );
                                v___x_6909_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                                crate::leanh::lean_ctor_set(v___x_6909_, 0, v___x_6907_);
                                crate::leanh::lean_ctor_set_uint64(
                                    v___x_6909_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_6908_,
                                );
                                v___x_6910_ = crate::leanh::lean_box(1);
                                v___x_6911_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                                v___x_6913_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                                v___x_6914_ = crate::leanh::lean_box(0);
                                v___x_6915_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                                crate::leanh::lean_ctor_set(v___x_6915_, 0, v___x_6909_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 1, v___x_6910_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 2, v___x_6912_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 3, v___x_6913_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 4, v___x_6914_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 5, v___x_6911_);
                                crate::leanh::lean_ctor_set(v___x_6915_, 6, v___x_6914_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6915_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7)
                                        as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6915_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1)
                                        as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6915_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2)
                                        as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6915_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3)
                                        as u32,
                                    v_hasTrace_6676_,
                                );
                                v___x_6916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                                v___x_6917_ = lean_st_mk_ref(v___x_6916_);
                                v___x_6918_ = l_Lean_Meta_getEqnsFor_x3f(
                                    v_fst_6876_,
                                    v___x_6915_,
                                    v___x_6917_,
                                    v___y_6672_,
                                    v___y_6673_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_6915_, 7);
                                if crate::leanh::lean_obj_tag(v___x_6918_) == 0 {
                                    v_a_6919_ = crate::leanh::lean_ctor_get(v___x_6918_, 0);
                                    crate::leanh::lean_inc(v_a_6919_);
                                    crate::leanh::lean_dec_ref_known(v___x_6918_, 1);
                                    v___x_6920_ = lean_st_ref_get(v___x_6917_);
                                    crate::leanh::lean_dec(v___x_6917_);
                                    crate::leanh::lean_dec(v___x_6920_);
                                    v___y_6810_ = v___x_6870_;
                                    v___y_6811_ = v___x_6871_;
                                    v___y_6812_ = v_a_6868_;
                                    v_a_6813_ = v_a_6919_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_6917_);
                                    if crate::leanh::lean_obj_tag(v___x_6918_) == 0 {
                                        v_a_6921_ = crate::leanh::lean_ctor_get(v___x_6918_, 0);
                                        crate::leanh::lean_inc(v_a_6921_);
                                        crate::leanh::lean_dec_ref_known(v___x_6918_, 1);
                                        v___y_6810_ = v___x_6870_;
                                        v___y_6811_ = v___x_6871_;
                                        v___y_6812_ = v_a_6868_;
                                        v_a_6813_ = v_a_6921_;
                                        state = 16;
                                        continue;
                                    } else {
                                        v_a_6922_ = crate::leanh::lean_ctor_get(v___x_6918_, 0);
                                        crate::leanh::lean_inc(v_a_6922_);
                                        crate::leanh::lean_dec_ref_known(v___x_6918_, 1);
                                        v___y_6820_ = v___x_6871_;
                                        v___y_6821_ = v_a_6868_;
                                        v_a_6822_ = v_a_6922_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6874_);
                        crate::leanh::lean_dec(v_name_6671_);
                        v___y_6804_ = v___x_6871_;
                        v___y_6805_ = v_a_6868_;
                        v_a_6806_ = v___x_6870_;
                        state = 15;
                        continue;
                    }
                } else {
                    v___x_6923_ = lean_io_get_num_heartbeats();
                    v___x_6924_ = lean_st_ref_get(v___y_6673_);
                    v_env_6925_ = crate::leanh::lean_ctor_get(v___x_6924_, 0);
                    crate::leanh::lean_inc_ref(v_env_6925_);
                    crate::leanh::lean_dec(v___x_6924_);
                    crate::leanh::lean_inc(v_name_6671_);
                    v___x_6926_ = l_Lean_Meta_declFromEqLikeName(v_env_6925_, v_name_6671_);
                    if crate::leanh::lean_obj_tag(v___x_6926_) == 1 {
                        v_val_6927_ = crate::leanh::lean_ctor_get(v___x_6926_, 0);
                        crate::leanh::lean_inc(v_val_6927_);
                        crate::leanh::lean_dec_ref_known(v___x_6926_, 1);
                        v_fst_6928_ = crate::leanh::lean_ctor_get(v_val_6927_, 0);
                        crate::leanh::lean_inc_n(v_fst_6928_, 2);
                        v_snd_6929_ = crate::leanh::lean_ctor_get(v_val_6927_, 1);
                        crate::leanh::lean_inc_n(v_snd_6929_, 2);
                        crate::leanh::lean_dec(v_val_6927_);
                        v___x_6930_ = lean_st_ref_get(v___y_6673_);
                        v_env_6931_ = crate::leanh::lean_ctor_get(v___x_6930_, 0);
                        crate::leanh::lean_inc_ref(v_env_6931_);
                        crate::leanh::lean_dec(v___x_6930_);
                        v___x_6932_ =
                            l_Lean_Meta_mkEqLikeNameFor(v_env_6931_, v_fst_6928_, v_snd_6929_);
                        v___x_6933_ = lean_name_eq(v_name_6671_, v___x_6932_);
                        crate::leanh::lean_dec(v___x_6932_);
                        crate::leanh::lean_dec(v_name_6671_);
                        if v___x_6933_ == 0 {
                            crate::leanh::lean_dec(v_snd_6929_);
                            crate::leanh::lean_dec(v_fst_6928_);
                            v___x_6934_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_6673_);
                            crate::leanh::lean_inc_ref(v___y_6672_);
                            v___x_6935_ = crate::leanh::lean_apply_4(
                                v___f_6670_,
                                v___x_6934_,
                                v___y_6672_,
                                v___y_6673_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_6860_ = v___x_6923_;
                            v___y_6861_ = v_a_6868_;
                            v___y_6862_ = v___x_6935_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_6929_);
                            v___x_6936_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_6929_);
                            if v___x_6936_ == 0 {
                                v___x_6937_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                                v___x_6938_ = lean_string_dec_eq(v_snd_6929_, v___x_6937_);
                                crate::leanh::lean_dec(v_snd_6929_);
                                if v___x_6938_ == 0 {
                                    crate::leanh::lean_dec(v_fst_6928_);
                                    v___x_6939_ = crate::leanh::lean_box(0);
                                    crate::leanh::lean_inc(v___y_6673_);
                                    crate::leanh::lean_inc_ref(v___y_6672_);
                                    v___x_6940_ = crate::leanh::lean_apply_4(
                                        v___f_6670_,
                                        v___x_6939_,
                                        v___y_6672_,
                                        v___y_6673_,
                                        crate::leanh::lean_box(0),
                                    );
                                    v___y_6860_ = v___x_6923_;
                                    v___y_6861_ = v_a_6868_;
                                    v___y_6862_ = v___x_6940_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___f_6670_);
                                    v___x_6941_ = 1;
                                    v___x_6942_ = 0;
                                    v___x_6943_ = 2;
                                    v___x_6944_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        0 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        1 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        2 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        3 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        4 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        5 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        6 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        7 as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        8 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        9 as u32,
                                        v___x_6941_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        10 as u32,
                                        v___x_6942_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        11 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        12 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        13 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        14 as u32,
                                        v___x_6943_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        15 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        16 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        17 as u32,
                                        v___x_6870_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6944_,
                                        18 as u32,
                                        v___x_6870_,
                                    );
                                    v___x_6945_ =
                                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                            v___x_6944_,
                                        );
                                    v___x_6946_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6946_, 0, v___x_6944_);
                                    crate::leanh::lean_ctor_set_uint64(
                                        v___x_6946_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                        v___x_6945_,
                                    );
                                    v___x_6947_ = crate::leanh::lean_box(1);
                                    v___x_6948_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_6949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                                    v___x_6950_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                                    v___x_6951_ = crate::leanh::lean_box(0);
                                    v___x_6952_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 0, v___x_6946_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 1, v___x_6947_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 2, v___x_6949_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 3, v___x_6950_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 4, v___x_6951_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 5, v___x_6948_);
                                    crate::leanh::lean_ctor_set(v___x_6952_, 6, v___x_6951_);
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6952_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7)
                                            as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6952_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 1) as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6952_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 2) as u32,
                                        v___x_6936_,
                                    );
                                    crate::leanh::lean_ctor_set_uint8(
                                        v___x_6952_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                                            + 3) as u32,
                                        v___x_6870_,
                                    );
                                    v___x_6953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                                    v___x_6954_ = lean_st_mk_ref(v___x_6953_);
                                    v___x_6955_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                                        v_fst_6928_,
                                        v___x_6870_,
                                        v___x_6952_,
                                        v___x_6954_,
                                        v___y_6672_,
                                        v___y_6673_,
                                    );
                                    crate::leanh::lean_dec_ref_known(v___x_6952_, 7);
                                    if crate::leanh::lean_obj_tag(v___x_6955_) == 0 {
                                        v_a_6956_ = crate::leanh::lean_ctor_get(v___x_6955_, 0);
                                        crate::leanh::lean_inc(v_a_6956_);
                                        crate::leanh::lean_dec_ref_known(v___x_6955_, 1);
                                        v___x_6957_ = lean_st_ref_get(v___x_6954_);
                                        crate::leanh::lean_dec(v___x_6954_);
                                        crate::leanh::lean_dec(v___x_6957_);
                                        v___y_6843_ = v___x_6923_;
                                        v___y_6844_ = v___x_6870_;
                                        v___y_6845_ = v___x_6936_;
                                        v___y_6846_ = v_a_6868_;
                                        v_a_6847_ = v_a_6956_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6954_);
                                        if crate::leanh::lean_obj_tag(v___x_6955_) == 0 {
                                            v_a_6958_ = crate::leanh::lean_ctor_get(v___x_6955_, 0);
                                            crate::leanh::lean_inc(v_a_6958_);
                                            crate::leanh::lean_dec_ref_known(v___x_6955_, 1);
                                            v___y_6843_ = v___x_6923_;
                                            v___y_6844_ = v___x_6870_;
                                            v___y_6845_ = v___x_6936_;
                                            v___y_6846_ = v_a_6868_;
                                            v_a_6847_ = v_a_6958_;
                                            state = 21;
                                            continue;
                                        } else {
                                            v_a_6959_ = crate::leanh::lean_ctor_get(v___x_6955_, 0);
                                            crate::leanh::lean_inc(v_a_6959_);
                                            crate::leanh::lean_dec_ref_known(v___x_6955_, 1);
                                            v___y_6855_ = v___x_6923_;
                                            v___y_6856_ = v_a_6868_;
                                            v_a_6857_ = v_a_6959_;
                                            state = 23;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_6929_);
                                crate::leanh::lean_dec_ref(v___f_6670_);
                                v___x_6960_ = 0;
                                v___x_6961_ = 1;
                                v___x_6962_ = 0;
                                v___x_6963_ = 2;
                                v___x_6964_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    0 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    1 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    2 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    3 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    4 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    5 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    6 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    7 as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    8 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    9 as u32,
                                    v___x_6961_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    10 as u32,
                                    v___x_6962_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    11 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    12 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    13 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    14 as u32,
                                    v___x_6963_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    15 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    16 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    17 as u32,
                                    v___x_6870_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6964_,
                                    18 as u32,
                                    v___x_6870_,
                                );
                                v___x_6965_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(
                                    v___x_6964_,
                                );
                                v___x_6966_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                                crate::leanh::lean_ctor_set(v___x_6966_, 0, v___x_6964_);
                                crate::leanh::lean_ctor_set_uint64(
                                    v___x_6966_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_6965_,
                                );
                                v___x_6967_ = crate::leanh::lean_box(1);
                                v___x_6968_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_6969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                                v___x_6970_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                                v___x_6971_ = crate::leanh::lean_box(0);
                                v___x_6972_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                                crate::leanh::lean_ctor_set(v___x_6972_, 0, v___x_6966_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 1, v___x_6967_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 2, v___x_6969_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 3, v___x_6970_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 4, v___x_6971_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 5, v___x_6968_);
                                crate::leanh::lean_ctor_set(v___x_6972_, 6, v___x_6971_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6972_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7)
                                        as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6972_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1)
                                        as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6972_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2)
                                        as u32,
                                    v___x_6960_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_6972_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3)
                                        as u32,
                                    v___x_6870_,
                                );
                                v___x_6973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                                v___x_6974_ = lean_st_mk_ref(v___x_6973_);
                                v___x_6975_ = l_Lean_Meta_getEqnsFor_x3f(
                                    v_fst_6928_,
                                    v___x_6972_,
                                    v___x_6974_,
                                    v___y_6672_,
                                    v___y_6673_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_6972_, 7);
                                if crate::leanh::lean_obj_tag(v___x_6975_) == 0 {
                                    v_a_6976_ = crate::leanh::lean_ctor_get(v___x_6975_, 0);
                                    crate::leanh::lean_inc(v_a_6976_);
                                    crate::leanh::lean_dec_ref_known(v___x_6975_, 1);
                                    v___x_6977_ = lean_st_ref_get(v___x_6974_);
                                    crate::leanh::lean_dec(v___x_6974_);
                                    crate::leanh::lean_dec(v___x_6977_);
                                    v___y_6849_ = v___x_6923_;
                                    v___y_6850_ = v___x_6870_;
                                    v___y_6851_ = v_a_6868_;
                                    v_a_6852_ = v_a_6976_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_6974_);
                                    if crate::leanh::lean_obj_tag(v___x_6975_) == 0 {
                                        v_a_6978_ = crate::leanh::lean_ctor_get(v___x_6975_, 0);
                                        crate::leanh::lean_inc(v_a_6978_);
                                        crate::leanh::lean_dec_ref_known(v___x_6975_, 1);
                                        v___y_6849_ = v___x_6923_;
                                        v___y_6850_ = v___x_6870_;
                                        v___y_6851_ = v_a_6868_;
                                        v_a_6852_ = v_a_6978_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_a_6979_ = crate::leanh::lean_ctor_get(v___x_6975_, 0);
                                        crate::leanh::lean_inc(v_a_6979_);
                                        crate::leanh::lean_dec_ref_known(v___x_6975_, 1);
                                        v___y_6855_ = v___x_6923_;
                                        v___y_6856_ = v_a_6868_;
                                        v_a_6857_ = v_a_6979_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6926_);
                        crate::leanh::lean_dec(v_name_6671_);
                        v___x_6980_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v___y_6673_);
                        crate::leanh::lean_inc_ref(v___y_6672_);
                        v___x_6981_ = crate::leanh::lean_apply_4(
                            v___f_6670_,
                            v___x_6980_,
                            v___y_6672_,
                            v___y_6673_,
                            crate::leanh::lean_box(0),
                        );
                        v___y_6860_ = v___x_6923_;
                        v___y_6861_ = v_a_6868_;
                        v___y_6862_ = v___x_6981_;
                        state = 24;
                        continue;
                    }
                }
            }
            26 => {
                if crate::leanh::lean_obj_tag(v_a_6985_) == 0 {
                    v___x_6986_ = crate::leanh::lean_box((v___x_6983_) as usize);
                    v___x_6987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6987_, 0, v___x_6986_);
                    return v___x_6987_;
                } else {
                    v_isSharedCheck_6995_ = (!crate::leanh::lean_is_exclusive(v_a_6985_)) as u8;
                    if v_isSharedCheck_6995_ == 0 {
                        v_unused_6996_ = crate::leanh::lean_ctor_get(v_a_6985_, 0);
                        crate::leanh::lean_dec(v_unused_6996_);
                        v___x_6989_ = v_a_6985_;
                        v_isShared_6990_ = v_isSharedCheck_6995_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6985_);
                        v___x_6989_ = crate::leanh::lean_box(0);
                        v_isShared_6990_ = v_isSharedCheck_6995_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                v___x_6991_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                if v_isShared_6990_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6989_, 0);
                    crate::leanh::lean_ctor_set(v___x_6989_, 0, v___x_6991_);
                    v___x_6993_ = v___x_6989_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6994_, 0, v___x_6991_);
                    v___x_6993_ = v_reuseFailAlloc_6994_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6993_;
            }
            29 => {
                if crate::leanh::lean_obj_tag(v_a_6998_) == 0 {
                    v___x_6999_ = crate::leanh::lean_box((v___x_6983_) as usize);
                    v___x_7000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7000_, 0, v___x_6999_);
                    return v___x_7000_;
                } else {
                    v_isSharedCheck_7008_ = (!crate::leanh::lean_is_exclusive(v_a_6998_)) as u8;
                    if v_isSharedCheck_7008_ == 0 {
                        v_unused_7009_ = crate::leanh::lean_ctor_get(v_a_6998_, 0);
                        crate::leanh::lean_dec(v_unused_7009_);
                        v___x_7002_ = v_a_6998_;
                        v_isShared_7003_ = v_isSharedCheck_7008_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_6998_);
                        v___x_7002_ = crate::leanh::lean_box(0);
                        v_isShared_7003_ = v_isSharedCheck_7008_;
                        state = 30;
                        continue;
                    }
                }
            }
            30 => {
                v___x_7004_ = crate::leanh::lean_box((v_hasTrace_6676_) as usize);
                if v_isShared_7003_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7002_, 0);
                    crate::leanh::lean_ctor_set(v___x_7002_, 0, v___x_7004_);
                    v___x_7006_ = v___x_7002_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 0, v___x_7004_);
                    v___x_7006_ = v_reuseFailAlloc_7007_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7006_;
            }
            32 => {
                v_fst_7017_ = crate::leanh::lean_ctor_get(v_val_7013_, 0);
                crate::leanh::lean_inc_n(v_fst_7017_, 2);
                v_snd_7018_ = crate::leanh::lean_ctor_get(v_val_7013_, 1);
                crate::leanh::lean_inc_n(v_snd_7018_, 2);
                crate::leanh::lean_dec(v_val_7013_);
                v___x_7019_ = lean_st_ref_get(v___y_6673_);
                v_env_7020_ = crate::leanh::lean_ctor_get(v___x_7019_, 0);
                crate::leanh::lean_inc_ref(v_env_7020_);
                crate::leanh::lean_dec(v___x_7019_);
                v___x_7021_ = l_Lean_Meta_mkEqLikeNameFor(v_env_7020_, v_fst_7017_, v_snd_7018_);
                v___x_7022_ = lean_name_eq(v_name_6671_, v___x_7021_);
                crate::leanh::lean_dec(v___x_7021_);
                crate::leanh::lean_dec(v_name_6671_);
                if v___x_7022_ == 0 {
                    crate::leanh::lean_dec(v_snd_7018_);
                    crate::leanh::lean_dec(v_fst_7017_);
                    v___x_7023_ = crate::leanh::lean_box((v___x_6983_) as usize);
                    if v_isShared_7016_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_7015_, 0);
                        crate::leanh::lean_ctor_set(v___x_7015_, 0, v___x_7023_);
                        v___x_7025_ = v___x_7015_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_7026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7026_, 0, v___x_7023_);
                        v___x_7025_ = v_reuseFailAlloc_7026_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_snd_7018_);
                    v___x_7027_ = l_Lean_Meta_isEqnReservedNameSuffix(v_snd_7018_);
                    if v___x_7027_ == 0 {
                        v___x_7028_ = l_Lean_Meta_unfoldThmSuffix___closed__0;
                        v___x_7029_ = lean_string_dec_eq(v_snd_7018_, v___x_7028_);
                        crate::leanh::lean_dec(v_snd_7018_);
                        if v___x_7029_ == 0 {
                            crate::leanh::lean_dec(v_fst_7017_);
                            v___x_7030_ = crate::leanh::lean_box((v___x_6983_) as usize);
                            if v_isShared_7016_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_7015_, 0);
                                crate::leanh::lean_ctor_set(v___x_7015_, 0, v___x_7030_);
                                v___x_7032_ = v___x_7015_;
                                state = 34;
                                continue;
                            } else {
                                v_reuseFailAlloc_7033_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7033_, 0, v___x_7030_);
                                v___x_7032_ = v_reuseFailAlloc_7033_;
                                state = 34;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7015_);
                            v___x_7034_ = 1;
                            v___x_7035_ = 0;
                            v___x_7036_ = 2;
                            v___x_7037_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 0 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 1 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 2 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 3 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 4 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                5 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                6 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 7 as u32, v___x_6983_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                8 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 9 as u32, v___x_7034_);
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 10 as u32, v___x_7035_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                11 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                12 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                13 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(v___x_7037_, 14 as u32, v___x_7036_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                15 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                16 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                17 as u32,
                                v_hasTrace_6676_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7037_,
                                18 as u32,
                                v_hasTrace_6676_,
                            );
                            v___x_7038_ =
                                l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_7037_);
                            v___x_7039_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                            crate::leanh::lean_ctor_set(v___x_7039_, 0, v___x_7037_);
                            crate::leanh::lean_ctor_set_uint64(
                                v___x_7039_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_7038_,
                            );
                            v___x_7040_ = crate::leanh::lean_box(1);
                            v___x_7041_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_7042_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                            v___x_7043_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                            v___x_7044_ = crate::leanh::lean_box(0);
                            v___x_7045_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                            crate::leanh::lean_ctor_set(v___x_7045_, 0, v___x_7039_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 1, v___x_7040_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 2, v___x_7042_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 3, v___x_7043_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 4, v___x_7044_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 5, v___x_7041_);
                            crate::leanh::lean_ctor_set(v___x_7045_, 6, v___x_7044_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7045_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                                v___x_6983_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7045_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1)
                                    as u32,
                                v___x_6983_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7045_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2)
                                    as u32,
                                v___x_6983_,
                            );
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_7045_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3)
                                    as u32,
                                v_hasTrace_6676_,
                            );
                            v___x_7046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                            v___x_7047_ = lean_st_mk_ref(v___x_7046_);
                            v___x_7048_ = l_Lean_Meta_getUnfoldEqnFor_x3f(
                                v_fst_7017_,
                                v_hasTrace_6676_,
                                v___x_7045_,
                                v___x_7047_,
                                v___y_6672_,
                                v___y_6673_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_7045_, 7);
                            if crate::leanh::lean_obj_tag(v___x_7048_) == 0 {
                                v_a_7049_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                                crate::leanh::lean_inc(v_a_7049_);
                                crate::leanh::lean_dec_ref_known(v___x_7048_, 1);
                                v___x_7050_ = lean_st_ref_get(v___x_7047_);
                                crate::leanh::lean_dec(v___x_7047_);
                                crate::leanh::lean_dec(v___x_7050_);
                                v_a_6998_ = v_a_7049_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7047_);
                                if crate::leanh::lean_obj_tag(v___x_7048_) == 0 {
                                    v_a_7051_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                                    crate::leanh::lean_inc(v_a_7051_);
                                    crate::leanh::lean_dec_ref_known(v___x_7048_, 1);
                                    v_a_6998_ = v_a_7051_;
                                    state = 29;
                                    continue;
                                } else {
                                    v_a_7052_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                                    v_isSharedCheck_7059_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7048_)) as u8;
                                    if v_isSharedCheck_7059_ == 0 {
                                        v___x_7054_ = v___x_7048_;
                                        v_isShared_7055_ = v_isSharedCheck_7059_;
                                        state = 35;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7052_);
                                        crate::leanh::lean_dec(v___x_7048_);
                                        v___x_7054_ = crate::leanh::lean_box(0);
                                        v_isShared_7055_ = v_isSharedCheck_7059_;
                                        state = 35;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_7018_);
                        crate::leanh::lean_del_object(v___x_7015_);
                        v___x_7060_ = 1;
                        v___x_7061_ = 0;
                        v___x_7062_ = 2;
                        v___x_7063_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 0 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 1 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 2 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 3 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 4 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 5 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 6 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 7 as u32, v___x_6983_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 8 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 9 as u32, v___x_7060_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 10 as u32, v___x_7061_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 11 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 12 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 13 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 14 as u32, v___x_7062_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 15 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 16 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 17 as u32, v_hasTrace_6676_);
                        crate::leanh::lean_ctor_set_uint8(v___x_7063_, 18 as u32, v_hasTrace_6676_);
                        v___x_7064_ =
                            l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_7063_);
                        v___x_7065_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                        crate::leanh::lean_ctor_set(v___x_7065_, 0, v___x_7063_);
                        crate::leanh::lean_ctor_set_uint64(
                            v___x_7065_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_7064_,
                        );
                        v___x_7066_ = crate::leanh::lean_box(1);
                        v___x_7067_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2_once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
                        v___x_7069_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
                        v___x_7070_ = crate::leanh::lean_box(0);
                        v___x_7071_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                        crate::leanh::lean_ctor_set(v___x_7071_, 0, v___x_7065_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 1, v___x_7066_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 2, v___x_7068_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 3, v___x_7069_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 4, v___x_7070_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 5, v___x_7067_);
                        crate::leanh::lean_ctor_set(v___x_7071_, 6, v___x_7070_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7071_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                            v___x_6983_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7071_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                            v___x_6983_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7071_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                            v___x_6983_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_7071_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                            v_hasTrace_6676_,
                        );
                        v___x_7072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
                        v___x_7073_ = lean_st_mk_ref(v___x_7072_);
                        v___x_7074_ = l_Lean_Meta_getEqnsFor_x3f(
                            v_fst_7017_,
                            v___x_7071_,
                            v___x_7073_,
                            v___y_6672_,
                            v___y_6673_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_7071_, 7);
                        if crate::leanh::lean_obj_tag(v___x_7074_) == 0 {
                            v_a_7075_ = crate::leanh::lean_ctor_get(v___x_7074_, 0);
                            crate::leanh::lean_inc(v_a_7075_);
                            crate::leanh::lean_dec_ref_known(v___x_7074_, 1);
                            v___x_7076_ = lean_st_ref_get(v___x_7073_);
                            crate::leanh::lean_dec(v___x_7073_);
                            crate::leanh::lean_dec(v___x_7076_);
                            v_a_6985_ = v_a_7075_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7073_);
                            if crate::leanh::lean_obj_tag(v___x_7074_) == 0 {
                                v_a_7077_ = crate::leanh::lean_ctor_get(v___x_7074_, 0);
                                crate::leanh::lean_inc(v_a_7077_);
                                crate::leanh::lean_dec_ref_known(v___x_7074_, 1);
                                v_a_6985_ = v_a_7077_;
                                state = 26;
                                continue;
                            } else {
                                v_a_7078_ = crate::leanh::lean_ctor_get(v___x_7074_, 0);
                                v_isSharedCheck_7085_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7074_)) as u8;
                                if v_isSharedCheck_7085_ == 0 {
                                    v___x_7080_ = v___x_7074_;
                                    v_isShared_7081_ = v_isSharedCheck_7085_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7078_);
                                    crate::leanh::lean_dec(v___x_7074_);
                                    v___x_7080_ = crate::leanh::lean_box(0);
                                    v_isShared_7081_ = v_isSharedCheck_7085_;
                                    state = 37;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            33 => {
                return v___x_7025_;
            }
            34 => {
                return v___x_7032_;
            }
            35 => {
                if v_isShared_7055_ == 0 {
                    v___x_7057_ = v___x_7054_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_7058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_a_7052_);
                    v___x_7057_ = v_reuseFailAlloc_7058_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_7057_;
            }
            37 => {
                if v_isShared_7081_ == 0 {
                    v___x_7083_ = v___x_7080_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_7084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7084_, 0, v_a_7078_);
                    v___x_7083_ = v_reuseFailAlloc_7084_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_7083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(
    mut v___f_7089_: *mut crate::leanh::LeanObject,
    mut v_name_7090_: *mut crate::leanh::LeanObject,
    mut v___y_7091_: *mut crate::leanh::LeanObject,
    mut v___y_7092_: *mut crate::leanh::LeanObject,
    mut v___y_7093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7094_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_(v___f_7089_, v_name_7090_, v___y_7091_, v___y_7092_);
    crate::leanh::lean_dec(v___y_7092_);
    crate::leanh::lean_dec_ref(v___y_7091_);
    return v_res_7094_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7138_ = crate::leanh::lean_unsigned_to_nat(3137104340);
    v___x_7139_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_7140_ = l_Lean_Name_num___override(v___x_7139_, v___x_7138_);
    return v___x_7140_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7142_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_7143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_7144_ = l_Lean_Name_str___override(v___x_7143_, v___x_7142_);
    return v___x_7144_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7146_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_7147_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_7148_ = l_Lean_Name_str___override(v___x_7147_, v___x_7146_);
    return v___x_7148_;
}
pub unsafe fn _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7149_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_7150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
    v___x_7151_ = l_Lean_Name_num___override(v___x_7150_, v___x_7149_);
    return v___x_7151_;
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7153_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_;
    v___x_7154_ = l_Lean_registerReservedNameAction(v___f_7153_);
    if crate::leanh::lean_obj_tag(v___x_7154_) == 0 {
        let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7156_: u8 = 0;
        let mut v___x_7157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_7154_, 1);
        v___x_7155_ = l_Lean_Meta_saveEqnAffectingOptions___closed__5;
        v___x_7156_ = 0;
        v___x_7157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_);
        v___x_7158_ = l_Lean_registerTraceClass(v___x_7155_, v___x_7156_, v___x_7157_);
        return v___x_7158_;
    } else {
        return v___x_7154_;
    }
}
pub unsafe fn l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2____boxed(
    mut v_a_7159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7160_ = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
    return v_res_7160_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(
    mut v_00_u03b1_7161_: *mut crate::leanh::LeanObject,
    mut v_x_7162_: *mut crate::leanh::LeanObject,
    mut v___y_7163_: *mut crate::leanh::LeanObject,
    mut v___y_7164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7166_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___redArg(v_x_7162_);
    return v___x_7166_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3___boxed(
    mut v_00_u03b1_7167_: *mut crate::leanh::LeanObject,
    mut v_x_7168_: *mut crate::leanh::LeanObject,
    mut v___y_7169_: *mut crate::leanh::LeanObject,
    mut v___y_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7172_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b1_7167_, v_x_7168_, v___y_7169_, v___y_7170_);
    crate::leanh::lean_dec(v___y_7170_);
    crate::leanh::lean_dec_ref(v___y_7169_);
    return v_res_7172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Eqns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DefEqAttrib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LetToHave(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1128896756____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_backward_eqns_nonrecursive = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_backward_eqns_nonrecursive);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_1234379183____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_backward_eqns_deepRecursiveSplit = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_backward_eqns_deepRecursiveSplit);
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_eqnAffectingOptions = _init_l_Lean_Meta_eqnAffectingOptions();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_177189230____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_eqnOptionsExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_eqnOptionsExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_758090479____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3508565914____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef);
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedEqnsExtState_default =
        _init_l_Lean_Meta_instInhabitedEqnsExtState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState_default);
    l_Lean_Meta_instInhabitedEqnsExtState = _init_l_Lean_Meta_instInhabitedEqnsExtState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3570318411____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_eqnsExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_eqnsExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_408789758____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn_00___x40_Lean_Meta_Eqns_3137104340____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Eqns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Eqns(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DefEqAttrib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LetToHave(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Eqns(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Eqns(builtin);
}
