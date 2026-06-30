// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.LRAT.Cert
// Imports: Std.Tactic.BVDecide.LRAT.Checker Lean.CoreM Std.Tactic.BVDecide.Syntax Lean.Meta.Tactic.BVDecide.LRAT.Trim Std.Tactic.BVDecide.LRAT.Parser Lean.Meta.Tactic.BVDecide.External
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_to_list, lean_array_uget_borrowed,
    lean_array_uset, lean_float_decLt, lean_float_div, lean_float_sub, lean_io_create_tempfile,
    lean_io_get_num_heartbeats, lean_io_mono_nanos_now, lean_io_prim_handle_flush,
    lean_io_prim_handle_put_str, lean_io_remove_file, lean_mk_empty_array_with_capacity,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Init::System::IO::{l_IO_FS_readBinFile, l_IO_lazyPure___redArg};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp7, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::External::{
    initialize_Lean_Meta_Tactic_BVDecide_External, l_Lean_Meta_Tactic_BVDecide_External_satQuery,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_External,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::Trim::{
    initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim, l_Lean_Meta_Tactic_BVDecide_LRAT_trim,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim,
};
use crate::r#gen::Lean::ToExpr::{
    l___private_Lean_ToExpr_0__Lean_List_toExprAux, l_Lean_instToExprArrayOfToLevel___redArg,
    l_Lean_instToExprInt, l_Lean_instToExprNat, l_Lean_instToExprProdOfToLevel___redArg,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
use crate::r#gen::Std::Sat::CNF::Dimacs::l_Std_Sat_CNF_dimacs;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Checker::{
    initialize_Std_Tactic_BVDecide_LRAT_Checker,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Parser::{
    initialize_Std_Tactic_BVDecide_LRAT_Parser, l_Std_Tactic_BVDecide_LRAT_lratProofToString,
    l_Std_Tactic_BVDecide_LRAT_parseLRATProof, runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser,
};
use crate::r#gen::Std::Tactic::BVDecide::Syntax::{
    initialize_Std_Tactic_BVDecide_Syntax, runtime_initialize_Std_Tactic_BVDecide_Syntax,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__0_value) as *mut leanh::LeanObject,8749134177695247953 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__4_value) as *mut leanh::LeanObject,7009148538150066493 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__8_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 82, 65, 84, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 100, 100, 69, 109, 112, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value) as *mut leanh::LeanObject,4333070676011756284 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__16_value) as *mut leanh::LeanObject,1718806322382269800 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 111, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__21_value) as *mut leanh::LeanObject,8414467900391110369 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__24_value) as *mut leanh::LeanObject,18135193680607614554 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__20_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__28_value) as *mut leanh::LeanObject,8614124190858717794 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 100, 100, 82, 117, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value) as *mut leanh::LeanObject,4333070676011756284 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__32_value) as *mut leanh::LeanObject,18330815752701016741 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 100, 100, 82, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value) as *mut leanh::LeanObject,4333070676011756284 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__38_value) as *mut leanh::LeanObject,6284193900954434686 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value) as *mut leanh::LeanObject,15289851429949568889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__45_value) as *mut leanh::LeanObject,6466355875042130293 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__44_value) as *mut leanh::LeanObject,15289851429949568889 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__54_value) as *mut leanh::LeanObject,15761733860085307253 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__41_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__57_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__15_value) as *mut leanh::LeanObject,4333070676011756284 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__60_value) as *mut leanh::LeanObject,6039355309666985576 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 116, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__11_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__13_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__14_value) as *mut leanh::LeanObject,14108742078913166941 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__3_value) as *mut leanh::LeanObject,4035310356935096666 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        84, 114, 105, 109, 109, 105, 110, 103, 32, 76, 82, 65, 84, 32, 112, 114, 111, 111, 102, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        80, 97, 114, 115, 105, 110, 103, 32, 76, 82, 65, 84, 32, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value:
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
    m_data: [115, 97, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__1_value)
            as *mut leanh::LeanObject,
        142734480563613395 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__12_value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__2_value)
            as *mut leanh::LeanObject,
        9704604365865994158 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__4_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        76, 82, 65, 84, 32, 112, 114, 111, 111, 102, 32, 104, 97, 115, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        32, 115, 116, 101, 112, 115, 32, 97, 102, 116, 101, 114, 32, 116, 114, 105, 109, 109, 105,
        110, 103, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9: f64 = 0.0;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_value:
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
        32, 115, 116, 101, 112, 115, 32, 98, 101, 102, 111, 114, 101, 32, 116, 114, 105, 109, 109,
        105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 65, 84, 32, 115, 111, 108, 118, 101, 114, 32, 112, 114, 111, 100, 117, 99, 101, 100,
        32, 105, 110, 118, 97, 108, 105, 100, 32, 76, 82, 65, 84, 58, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        82, 117, 110, 110, 105, 110, 103, 32, 83, 65, 84, 32, 115, 111, 108, 118, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value:
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
        79, 98, 116, 97, 105, 110, 105, 110, 103, 32, 76, 82, 65, 84, 32, 99, 101, 114, 116, 105,
        102, 105, 99, 97, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        83, 101, 114, 105, 97, 108, 105, 122, 105, 110, 103, 32, 83, 65, 84, 32, 112, 114, 111, 98,
        108, 101, 109, 32, 116, 111, 32, 68, 73, 77, 65, 67, 83, 32, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2;
    v___x_2402_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__1;
    v___x_2403_ = l_Lean_mkConst(v___x_2402_, v___x_2401_);
    return v___x_2403_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2407_ = leanh::lean_box(0);
    v___x_2408_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5;
    v___x_2409_ = l_Lean_mkConst(v___x_2408_, v___x_2407_);
    return v___x_2409_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_beta_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__6);
    v___x_2411_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3);
    v_beta_2412_ = l_Lean_Expr_app___override(v___x_2411_, v___x_2410_);
    return v_beta_2412_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alpha_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = leanh::lean_box(0);
    v___x_2417_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__9;
    v_alpha_2418_ = l_Lean_mkConst(v___x_2417_, v___x_2416_);
    return v_alpha_2418_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2436_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__17;
    v___x_2437_ = l_Lean_mkConst(v___x_2436_, v___x_2435_);
    return v___x_2437_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2;
    v___x_2444_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__22;
    v___x_2445_ = l_Lean_mkConst(v___x_2444_, v___x_2443_);
    return v___x_2445_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2;
    v___x_2451_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__25;
    v___x_2452_ = l_Lean_mkConst(v___x_2451_, v___x_2450_);
    return v___x_2452_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27()
-> *mut leanh::LeanObject {
    let mut v_alpha_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alpha_2453_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
    v___x_2454_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
    v_nil_2455_ = l_Lean_Expr_app___override(v___x_2454_, v_alpha_2453_);
    return v_nil_2455_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__2;
    v___x_2461_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__29;
    v___x_2462_ = l_Lean_mkConst(v___x_2461_, v___x_2460_);
    return v___x_2462_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31()
-> *mut leanh::LeanObject {
    let mut v_alpha_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alpha_2463_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
    v___x_2464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
    v_cons_2465_ = l_Lean_Expr_app___override(v___x_2464_, v_alpha_2463_);
    return v_cons_2465_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2475_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__33;
    v___x_2476_ = l_Lean_mkConst(v___x_2475_, v___x_2474_);
    return v___x_2476_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = leanh::lean_box(0);
    v___x_2478_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__5;
    v_type_2479_ = l_Lean_Expr_const___override(v___x_2478_, v___x_2477_);
    return v_type_2479_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36()
-> *mut leanh::LeanObject {
    let mut v_type_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
    v___x_2481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
    v_nil_2482_ = l_Lean_Expr_app___override(v___x_2481_, v_type_2480_);
    return v_nil_2482_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37()
-> *mut leanh::LeanObject {
    let mut v_type_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
    v___x_2484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
    v_cons_2485_ = l_Lean_Expr_app___override(v___x_2484_, v_type_2483_);
    return v_cons_2485_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40()
-> *mut leanh::LeanObject {
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2495_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__39;
    v___x_2496_ = l_Lean_mkConst(v___x_2495_, v___x_2494_);
    return v___x_2496_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43()
-> *mut leanh::LeanObject {
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2Type_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2500_ = leanh::lean_box(0);
    v___x_2501_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__42;
    v_00_u03b2Type_2502_ = l_Lean_mkConst(v___x_2501_, v___x_2500_);
    return v_00_u03b2Type_2502_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2509_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__46;
    v___x_2510_ = l_Lean_mkConst(v___x_2509_, v___x_2508_);
    return v___x_2510_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48()
-> *mut leanh::LeanObject {
    let mut v_alpha_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2Type_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alpha_2511_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
    v___x_2512_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__3);
    v_00_u03b2Type_2513_ = l_Lean_Expr_app___override(v___x_2512_, v_alpha_2511_);
    return v_00_u03b2Type_2513_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50()
-> *mut leanh::LeanObject {
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2517_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__49;
    v___x_2518_ = l_Lean_mkConst(v___x_2517_, v___x_2516_);
    return v___x_2518_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51()
-> *mut leanh::LeanObject {
    let mut v_00_u03b2Type_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alpha_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_00_u03b2Type_2519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__48);
    v_alpha_2520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
    v___x_2521_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__50);
    v_type_2522_ = l_Lean_mkAppB(v___x_2521_, v_alpha_2520_, v_00_u03b2Type_2519_);
    return v_type_2522_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52()
-> *mut leanh::LeanObject {
    let mut v_type_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
    v___x_2524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__26);
    v_nil_2525_ = l_Lean_Expr_app___override(v___x_2524_, v_type_2523_);
    return v_nil_2525_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53()
-> *mut leanh::LeanObject {
    let mut v_type_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_2526_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
    v___x_2527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__30);
    v_cons_2528_ = l_Lean_Expr_app___override(v___x_2527_, v_type_2526_);
    return v_cons_2528_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56()
-> *mut leanh::LeanObject {
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = leanh::lean_box(0);
    v___x_2534_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__55;
    v___x_2535_ = l_Lean_mkConst(v___x_2534_, v___x_2533_);
    return v___x_2535_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59()
-> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = leanh::lean_box(0);
    v___x_2541_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__58;
    v___x_2542_ = l_Lean_mkConst(v___x_2541_, v___x_2540_);
    return v___x_2542_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2551_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__18;
    v___x_2552_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__61;
    v___x_2553_ = l_Lean_mkConst(v___x_2552_, v___x_2551_);
    return v___x_2553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0(
    mut v___x_2554_: *mut leanh::LeanObject,
    mut v___x_2555_: *mut leanh::LeanObject,
    mut v___x_2556_: *mut leanh::LeanObject,
    mut v_action_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_beta_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alpha_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2Type_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_beta_2558_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__7);
                v_alpha_2559_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__10);
                match leanh::lean_obj_tag(v_action_2557_) {
                    0 => {
                        leanh::lean_dec_ref(v___x_2556_);
                        leanh::lean_dec_ref(v___x_2555_);
                        v_id_2560_ = leanh::lean_ctor_get(v_action_2557_, 0);
                        leanh::lean_inc(v_id_2560_);
                        v_rupHints_2561_ = leanh::lean_ctor_get(v_action_2557_, 1);
                        leanh::lean_inc_ref(v_rupHints_2561_);
                        leanh::lean_dec_ref_known(v_action_2557_, 2);
                        v___x_2562_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__19);
                        v___x_2563_ = l_Lean_mkNatLit(v_id_2560_);
                        v___x_2564_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
                        v_nil_2565_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
                        v_cons_2566_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
                        v___x_2567_ = lean_array_to_list(v_rupHints_2561_);
                        v___x_2568_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                            leanh::lean_box(0),
                            v___x_2554_,
                            v_nil_2565_,
                            v_cons_2566_,
                            v___x_2567_,
                        );
                        v___x_2569_ = l_Lean_mkAppB(v___x_2564_, v_alpha_2559_, v___x_2568_);
                        v___x_2570_ = l_Lean_mkApp4(
                            v___x_2562_,
                            v_beta_2558_,
                            v_alpha_2559_,
                            v___x_2563_,
                            v___x_2569_,
                        );
                        return v___x_2570_;
                    }
                    1 => {
                        leanh::lean_dec_ref(v___x_2556_);
                        v_id_2571_ = leanh::lean_ctor_get(v_action_2557_, 0);
                        leanh::lean_inc(v_id_2571_);
                        v_c_2572_ = leanh::lean_ctor_get(v_action_2557_, 1);
                        leanh::lean_inc(v_c_2572_);
                        v_rupHints_2573_ = leanh::lean_ctor_get(v_action_2557_, 2);
                        leanh::lean_inc_ref(v_rupHints_2573_);
                        leanh::lean_dec_ref_known(v_action_2557_, 3);
                        v___x_2574_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__34);
                        v___x_2575_ = l_Lean_mkNatLit(v_id_2571_);
                        v_type_2576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
                        v___x_2577_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
                        v_nil_2578_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36);
                        v_cons_2579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37);
                        v___x_2580_ = lean_array_to_list(v_c_2572_);
                        v___x_2581_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                            leanh::lean_box(0),
                            v___x_2555_,
                            v_nil_2578_,
                            v_cons_2579_,
                            v___x_2580_,
                        );
                        v___x_2582_ = l_Lean_mkAppB(v___x_2577_, v_type_2576_, v___x_2581_);
                        v_nil_2583_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
                        v_cons_2584_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
                        v___x_2585_ = lean_array_to_list(v_rupHints_2573_);
                        v___x_2586_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                            leanh::lean_box(0),
                            v___x_2554_,
                            v_nil_2583_,
                            v_cons_2584_,
                            v___x_2585_,
                        );
                        v___x_2587_ = l_Lean_mkAppB(v___x_2577_, v_alpha_2559_, v___x_2586_);
                        v___x_2588_ = l_Lean_mkApp5(
                            v___x_2574_,
                            v_beta_2558_,
                            v_alpha_2559_,
                            v___x_2575_,
                            v___x_2582_,
                            v___x_2587_,
                        );
                        return v___x_2588_;
                    }
                    2 => {
                        v_id_2589_ = leanh::lean_ctor_get(v_action_2557_, 0);
                        leanh::lean_inc(v_id_2589_);
                        v_c_2590_ = leanh::lean_ctor_get(v_action_2557_, 1);
                        leanh::lean_inc(v_c_2590_);
                        v_pivot_2591_ = leanh::lean_ctor_get(v_action_2557_, 2);
                        leanh::lean_inc_ref(v_pivot_2591_);
                        v_rupHints_2592_ = leanh::lean_ctor_get(v_action_2557_, 3);
                        leanh::lean_inc_ref(v_rupHints_2592_);
                        v_ratHints_2593_ = leanh::lean_ctor_get(v_action_2557_, 4);
                        leanh::lean_inc_ref(v_ratHints_2593_);
                        leanh::lean_dec_ref_known(v_action_2557_, 5);
                        v___x_2594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
                        v_fst_2595_ = leanh::lean_ctor_get(v_pivot_2591_, 0);
                        leanh::lean_inc(v_fst_2595_);
                        v_snd_2596_ = leanh::lean_ctor_get(v_pivot_2591_, 1);
                        leanh::lean_inc(v_snd_2596_);
                        leanh::lean_dec_ref(v_pivot_2591_);
                        v_type_2597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__35);
                        v_nil_2598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__36);
                        v_cons_2599_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__37);
                        v___x_2600_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__40);
                        v___x_2601_ = l_Lean_mkNatLit(v_id_2589_);
                        v___x_2602_ = lean_array_to_list(v_c_2590_);
                        v___x_2603_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                            leanh::lean_box(0),
                            v___x_2555_,
                            v_nil_2598_,
                            v_cons_2599_,
                            v___x_2602_,
                        );
                        v___x_2604_ = l_Lean_mkAppB(v___x_2594_, v_type_2597_, v___x_2603_);
                        v_00_u03b2Type_2605_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__43);
                        v___x_2606_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__47);
                        v___x_2607_ = l_Lean_mkNatLit(v_fst_2595_);
                        v___x_2623_ = (leanh::lean_unbox(v_snd_2596_) as u8);
                        leanh::lean_dec(v_snd_2596_);
                        if v___x_2623_ == 0 {
                            v___x_2624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__56);
                            v___y_2609_ = v___x_2624_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2625_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__59);
                            v___y_2609_ = v___x_2625_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_2556_);
                        leanh::lean_dec_ref(v___x_2555_);
                        v_ids_2626_ = leanh::lean_ctor_get(v_action_2557_, 0);
                        leanh::lean_inc_ref(v_ids_2626_);
                        leanh::lean_dec_ref_known(v_action_2557_, 1);
                        v___x_2627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__62);
                        v___x_2628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__23);
                        v_nil_2629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
                        v_cons_2630_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
                        v___x_2631_ = lean_array_to_list(v_ids_2626_);
                        v___x_2632_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                            leanh::lean_box(0),
                            v___x_2554_,
                            v_nil_2629_,
                            v_cons_2630_,
                            v___x_2631_,
                        );
                        v___x_2633_ = l_Lean_mkAppB(v___x_2628_, v_alpha_2559_, v___x_2632_);
                        v___x_2634_ =
                            l_Lean_mkApp3(v___x_2627_, v_beta_2558_, v_alpha_2559_, v___x_2633_);
                        return v___x_2634_;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2609_);
                v___x_2610_ = l_Lean_mkApp4(
                    v___x_2606_,
                    v_alpha_2559_,
                    v_00_u03b2Type_2605_,
                    v___x_2607_,
                    v___y_2609_,
                );
                v_nil_2611_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__27);
                v_cons_2612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__31);
                v___x_2613_ = lean_array_to_list(v_rupHints_2592_);
                v___x_2614_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                    leanh::lean_box(0),
                    v___x_2554_,
                    v_nil_2611_,
                    v_cons_2612_,
                    v___x_2613_,
                );
                v___x_2615_ = l_Lean_mkAppB(v___x_2594_, v_alpha_2559_, v___x_2614_);
                v_type_2616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__51);
                v_nil_2617_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__52);
                v_cons_2618_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0___closed__53);
                v___x_2619_ = lean_array_to_list(v_ratHints_2593_);
                v___x_2620_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(
                    leanh::lean_box(0),
                    v___x_2556_,
                    v_nil_2617_,
                    v_cons_2618_,
                    v___x_2619_,
                );
                v___x_2621_ = l_Lean_mkAppB(v___x_2594_, v_type_2616_, v___x_2620_);
                v___x_2622_ = l_Lean_mkApp7(
                    v___x_2600_,
                    v_beta_2558_,
                    v_alpha_2559_,
                    v___x_2601_,
                    v___x_2604_,
                    v___x_2610_,
                    v___x_2615_,
                    v___x_2621_,
                );
                return v___x_2622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2635_ = l_Lean_instToExprNat;
    v___x_2636_ = leanh::lean_box(0);
    v___x_2637_ = l_Lean_instToExprArrayOfToLevel___redArg(v___x_2636_, v___x_2635_);
    return v___x_2637_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__0);
    v___x_2639_ = l_Lean_instToExprNat;
    v___x_2640_ = leanh::lean_box(0);
    v___x_2641_ =
        l_Lean_instToExprProdOfToLevel___redArg(v___x_2640_, v___x_2640_, v___x_2639_, v___x_2638_);
    return v___x_2641_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__1);
    v___x_2643_ = l_Lean_instToExprInt;
    v___x_2644_ = l_Lean_instToExprNat;
    v___f_2645_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___lam__0 as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_2645_, 0, v___x_2644_);
    leanh::lean_closure_set(v___f_2645_, 1, v___x_2643_);
    leanh::lean_closure_set(v___f_2645_, 2, v___x_2642_);
    return v___f_2645_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2653_ = leanh::lean_box(0);
    v___x_2654_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__4;
    v___x_2655_ = l_Lean_mkConst(v___x_2654_, v___x_2653_);
    return v___x_2655_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__5);
    v___f_2657_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__2);
    v___x_2658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2658_, 0, v___f_2657_);
    leanh::lean_ctor_set(v___x_2658_, 1, v___x_2656_);
    return v___x_2658_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction()
-> *mut leanh::LeanObject {
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction___closed__6);
    return v___x_2659_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2660_ = leanh::lean_unsigned_to_nat(32);
    v___x_2661_ = lean_mk_empty_array_with_capacity(v___x_2660_);
    v___x_2662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2662_, 0, v___x_2661_);
    return v___x_2662_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2663_: usize = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2663_ = 5usize;
    v___x_2664_ = leanh::lean_unsigned_to_nat(0);
    v___x_2665_ = leanh::lean_unsigned_to_nat(32);
    v___x_2666_ = lean_mk_empty_array_with_capacity(v___x_2665_);
    v___x_2667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__0);
    v___x_2668_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2668_, 0, v___x_2667_);
    leanh::lean_ctor_set(v___x_2668_, 1, v___x_2666_);
    leanh::lean_ctor_set(v___x_2668_, 2, v___x_2664_);
    leanh::lean_ctor_set(v___x_2668_, 3, v___x_2664_);
    leanh::lean_ctor_set_usize(v___x_2668_, 4, v___x_2663_);
    return v___x_2668_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(
    mut v___y_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v_tid_2687_: u64 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2690_: u8 = 0;
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_unused_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2671_ = lean_st_ref_get(v___y_2669_);
                v_traceState_2672_ = leanh::lean_ctor_get(v___x_2671_, 4);
                leanh::lean_inc_ref(v_traceState_2672_);
                leanh::lean_dec(v___x_2671_);
                v_traces_2673_ = leanh::lean_ctor_get(v_traceState_2672_, 0);
                leanh::lean_inc_ref(v_traces_2673_);
                leanh::lean_dec_ref(v_traceState_2672_);
                v___x_2674_ = lean_st_ref_take(v___y_2669_);
                v_traceState_2675_ = leanh::lean_ctor_get(v___x_2674_, 4);
                v_env_2676_ = leanh::lean_ctor_get(v___x_2674_, 0);
                v_nextMacroScope_2677_ = leanh::lean_ctor_get(v___x_2674_, 1);
                v_ngen_2678_ = leanh::lean_ctor_get(v___x_2674_, 2);
                v_auxDeclNGen_2679_ = leanh::lean_ctor_get(v___x_2674_, 3);
                v_cache_2680_ = leanh::lean_ctor_get(v___x_2674_, 5);
                v_messages_2681_ = leanh::lean_ctor_get(v___x_2674_, 6);
                v_infoState_2682_ = leanh::lean_ctor_get(v___x_2674_, 7);
                v_snapshotTasks_2683_ = leanh::lean_ctor_get(v___x_2674_, 8);
                v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v___x_2674_)) as u8;
                if v_isSharedCheck_2702_ == 0 {
                    v___x_2685_ = v___x_2674_;
                    v_isShared_2686_ = v_isSharedCheck_2702_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2683_);
                    leanh::lean_inc(v_infoState_2682_);
                    leanh::lean_inc(v_messages_2681_);
                    leanh::lean_inc(v_cache_2680_);
                    leanh::lean_inc(v_traceState_2675_);
                    leanh::lean_inc(v_auxDeclNGen_2679_);
                    leanh::lean_inc(v_ngen_2678_);
                    leanh::lean_inc(v_nextMacroScope_2677_);
                    leanh::lean_inc(v_env_2676_);
                    leanh::lean_dec(v___x_2674_);
                    v___x_2685_ = leanh::lean_box(0);
                    v_isShared_2686_ = v_isSharedCheck_2702_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_2687_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2700_ =
                    (!leanh::lean_is_exclusive(v_traceState_2675_)) as u8;
                if v_isSharedCheck_2700_ == 0 {
                    v_unused_2701_ = leanh::lean_ctor_get(v_traceState_2675_, 0);
                    leanh::lean_dec(v_unused_2701_);
                    v___x_2689_ = v_traceState_2675_;
                    v_isShared_2690_ = v_isSharedCheck_2700_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_2675_);
                    v___x_2689_ = leanh::lean_box(0);
                    v_isShared_2690_ = v_isSharedCheck_2700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2691_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___closed__1);
                if v_isShared_2690_ == 0 {
                    leanh::lean_ctor_set(v___x_2689_, 0, v___x_2691_);
                    v___x_2693_ = v___x_2689_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2699_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2691_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2699_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2687_,
                    );
                    v___x_2693_ = v_reuseFailAlloc_2699_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2686_ == 0 {
                    leanh::lean_ctor_set(v___x_2685_, 4, v___x_2693_);
                    v___x_2695_ = v___x_2685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2698_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_env_2676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_nextMacroScope_2677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_ngen_2678_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 3, v_auxDeclNGen_2679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 4, v___x_2693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 5, v_cache_2680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 6, v_messages_2681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 7, v_infoState_2682_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2698_, 8, v_snapshotTasks_2683_);
                    v___x_2695_ = v_reuseFailAlloc_2698_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2696_ = lean_st_ref_set(v___y_2669_, v___x_2695_);
                v___x_2697_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2697_, 0, v_traces_2673_);
                return v___x_2697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg___boxed(
    mut v___y_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2705_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_2703_);
    leanh::lean_dec(v___y_2703_);
    return v_res_2705_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_2707_);
    return v___x_2709_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___boxed(
    mut v___y_2710_: *mut leanh::LeanObject,
    mut v___y_2711_: *mut leanh::LeanObject,
    mut v___y_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2713_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1(v___y_2710_, v___y_2711_);
    leanh::lean_dec(v___y_2711_);
    leanh::lean_dec_ref(v___y_2710_);
    return v_res_2713_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
    mut v_opts_2714_: *mut leanh::LeanObject,
    mut v_opt_2715_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2716_ = leanh::lean_ctor_get(v_opt_2715_, 0);
    v_defValue_2717_ = leanh::lean_ctor_get(v_opt_2715_, 1);
    v_map_2718_ = leanh::lean_ctor_get(v_opts_2714_, 0);
    v___x_2719_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2718_,
            v_name_2716_,
        );
    if leanh::lean_obj_tag(v___x_2719_) == 0 {
        let mut v___x_2720_: u8 = 0;
        v___x_2720_ = (leanh::lean_unbox(v_defValue_2717_) as u8);
        return v___x_2720_;
    } else {
        let mut v_val_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2721_ = leanh::lean_ctor_get(v___x_2719_, 0);
        leanh::lean_inc(v_val_2721_);
        leanh::lean_dec_ref_known(v___x_2719_, 1);
        if leanh::lean_obj_tag(v_val_2721_) == 1 {
            let mut v_v_2722_: u8 = 0;
            v_v_2722_ = leanh::lean_ctor_get_uint8(v_val_2721_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2721_, 0);
            return v_v_2722_;
        } else {
            let mut v___x_2723_: u8 = 0;
            leanh::lean_dec(v_val_2721_);
            v___x_2723_ = (leanh::lean_unbox(v_defValue_2717_) as u8);
            return v___x_2723_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2___boxed(
    mut v_opts_2724_: *mut leanh::LeanObject,
    mut v_opt_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2726_: u8 = 0;
    let mut v_r_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2726_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
        v_opts_2724_,
        v_opt_2725_,
    );
    leanh::lean_dec_ref(v_opt_2725_);
    leanh::lean_dec_ref(v_opts_2724_);
    v_r_2727_ = leanh::lean_box((v_res_2726_) as usize);
    return v_r_2727_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(
    mut v_e_2728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_2728_) == 0 {
                    v_a_2730_ = leanh::lean_ctor_get(v_e_2728_, 0);
                    v_isSharedCheck_2738_ = (!leanh::lean_is_exclusive(v_e_2728_)) as u8;
                    if v_isSharedCheck_2738_ == 0 {
                        v___x_2732_ = v_e_2728_;
                        v_isShared_2733_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2730_);
                        leanh::lean_dec(v_e_2728_);
                        v___x_2732_ = leanh::lean_box(0);
                        v_isShared_2733_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2739_ = leanh::lean_ctor_get(v_e_2728_, 0);
                    v_isSharedCheck_2746_ = (!leanh::lean_is_exclusive(v_e_2728_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v___x_2741_ = v_e_2728_;
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2739_);
                        leanh::lean_dec(v_e_2728_);
                        v___x_2741_ = leanh::lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2734_ = lean_mk_io_user_error(v_a_2730_);
                if v_isShared_2733_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2732_, 1);
                    leanh::lean_ctor_set(v___x_2732_, 0, v___x_2734_);
                    v___x_2736_ = v___x_2732_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
                    v___x_2736_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2736_;
            }
            3 => {
                if v_isShared_2742_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2741_, 0);
                    v___x_2744_ = v___x_2741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg___boxed(
    mut v_e_2747_: *mut leanh::LeanObject,
    mut v_a_2748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2749_ =
        l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_2747_);
    return v_res_2749_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(
    mut v_00_u03b1_2750_: *mut leanh::LeanObject,
    mut v_e_2751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2753_ =
        l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_e_2751_);
    return v___x_2753_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___boxed(
    mut v_00_u03b1_2754_: *mut leanh::LeanObject,
    mut v_e_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2757_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4(
        v_00_u03b1_2754_,
        v_e_2755_,
    );
    return v_res_2757_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__1;
    v___x_2762_ = l_Lean_MessageData_ofFormat(v___x_2761_);
    return v___x_2762_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(
    mut v_x_2763_: *mut leanh::LeanObject,
    mut v___y_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___closed__2,
    );
    v___x_2768_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2768_, 0, v___x_2767_);
    return v___x_2768_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0___boxed(
    mut v_x_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2773_ =
        l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__0(v_x_2769_, v___y_2770_, v___y_2771_);
    leanh::lean_dec(v___y_2771_);
    leanh::lean_dec_ref(v___y_2770_);
    leanh::lean_dec_ref(v_x_2769_);
    return v_res_2773_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1(
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_x_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2776_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v_a_2774_);
    return v___x_2776_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(
    mut v_a_2777_: *mut leanh::LeanObject,
    mut v_x_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_2777_);
    return v___x_2779_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed(
    mut v_a_2780_: *mut leanh::LeanObject,
    mut v_x_2781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2782_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2(v_a_2780_, v_x_2781_);
    leanh::lean_dec_ref(v_a_2780_);
    return v_res_2782_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__1;
    v___x_2787_ = l_Lean_MessageData_ofFormat(v___x_2786_);
    return v___x_2787_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(
    mut v_x_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___closed__2,
    );
    v___x_2793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2793_, 0, v___x_2792_);
    return v___x_2793_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3___boxed(
    mut v_x_2794_: *mut leanh::LeanObject,
    mut v___y_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ =
        l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__3(v_x_2794_, v___y_2795_, v___y_2796_);
    leanh::lean_dec(v___y_2796_);
    leanh::lean_dec_ref(v___y_2795_);
    leanh::lean_dec_ref(v_x_2794_);
    return v_res_2798_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(
    mut v_sz_2799_: usize,
    mut v_i_2800_: usize,
    mut v_bs_2801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2802_: u8 = 0;
    let mut v_v_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: usize = 0;
    let mut v___x_2808_: usize = 0;
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2802_ = lean_usize_dec_lt(v_i_2800_, v_sz_2799_);
                if v___x_2802_ == 0 {
                    return v_bs_2801_;
                } else {
                    v_v_2803_ = lean_array_uget_borrowed(v_bs_2801_, v_i_2800_);
                    v_msg_2804_ = leanh::lean_ctor_get(v_v_2803_, 1);
                    leanh::lean_inc_ref(v_msg_2804_);
                    v___x_2805_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2806_ = lean_array_uset(v_bs_2801_, v_i_2800_, v___x_2805_);
                    v___x_2807_ = 1usize;
                    v___x_2808_ = lean_usize_add(v_i_2800_, v___x_2807_);
                    v___x_2809_ = lean_array_uset(v_bs_x27_2806_, v_i_2800_, v_msg_2804_);
                    v_i_2800_ = v___x_2808_;
                    v_bs_2801_ = v___x_2809_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7___boxed(
    mut v_sz_2811_: *mut leanh::LeanObject,
    mut v_i_2812_: *mut leanh::LeanObject,
    mut v_bs_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2814_: usize = 0;
    let mut v_i_boxed_2815_: usize = 0;
    let mut v_res_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2814_ = leanh::lean_unbox_usize(v_sz_2811_);
    leanh::lean_dec(v_sz_2811_);
    v_i_boxed_2815_ = leanh::lean_unbox_usize(v_i_2812_);
    leanh::lean_dec(v_i_2812_);
    v_res_2816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(v_sz_boxed_2814_, v_i_boxed_2815_, v_bs_2813_);
    return v_res_2816_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2817_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__0);
    v___x_2819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2819_, 0, v___x_2818_);
    return v___x_2819_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
    v___x_2821_ = leanh::lean_unsigned_to_nat(0);
    v___x_2822_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2822_, 0, v___x_2821_);
    leanh::lean_ctor_set(v___x_2822_, 1, v___x_2821_);
    leanh::lean_ctor_set(v___x_2822_, 2, v___x_2821_);
    leanh::lean_ctor_set(v___x_2822_, 3, v___x_2821_);
    leanh::lean_ctor_set(v___x_2822_, 4, v___x_2820_);
    leanh::lean_ctor_set(v___x_2822_, 5, v___x_2820_);
    leanh::lean_ctor_set(v___x_2822_, 6, v___x_2820_);
    leanh::lean_ctor_set(v___x_2822_, 7, v___x_2820_);
    leanh::lean_ctor_set(v___x_2822_, 8, v___x_2820_);
    leanh::lean_ctor_set(v___x_2822_, 9, v___x_2820_);
    return v___x_2822_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = leanh::lean_unsigned_to_nat(32);
    v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2823_);
    v___x_2825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
    return v___x_2825_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2826_: usize = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2826_ = 5usize;
    v___x_2827_ = leanh::lean_unsigned_to_nat(0);
    v___x_2828_ = leanh::lean_unsigned_to_nat(32);
    v___x_2829_ = lean_mk_empty_array_with_capacity(v___x_2828_);
    v___x_2830_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__3);
    v___x_2831_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2831_, 0, v___x_2830_);
    leanh::lean_ctor_set(v___x_2831_, 1, v___x_2829_);
    leanh::lean_ctor_set(v___x_2831_, 2, v___x_2827_);
    leanh::lean_ctor_set(v___x_2831_, 3, v___x_2827_);
    leanh::lean_ctor_set_usize(v___x_2831_, 4, v___x_2826_);
    return v___x_2831_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = leanh::lean_box(1);
    v___x_2833_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__4);
    v___x_2834_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__1);
    v___x_2835_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2835_, 0, v___x_2834_);
    leanh::lean_ctor_set(v___x_2835_, 1, v___x_2833_);
    leanh::lean_ctor_set(v___x_2835_, 2, v___x_2832_);
    return v___x_2835_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(
    mut v_msgData_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2840_ = lean_st_ref_get(v___y_2838_);
    v_env_2841_ = leanh::lean_ctor_get(v___x_2840_, 0);
    leanh::lean_inc_ref(v_env_2841_);
    leanh::lean_dec(v___x_2840_);
    v_options_2842_ = leanh::lean_ctor_get(v___y_2837_, 2);
    v___x_2843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__2);
    v___x_2844_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_2842_);
    v___x_2845_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2845_, 0, v_env_2841_);
    leanh::lean_ctor_set(v___x_2845_, 1, v___x_2843_);
    leanh::lean_ctor_set(v___x_2845_, 2, v___x_2844_);
    leanh::lean_ctor_set(v___x_2845_, 3, v_options_2842_);
    v___x_2846_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2846_, 0, v___x_2845_);
    leanh::lean_ctor_set(v___x_2846_, 1, v_msgData_2836_);
    v___x_2847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2847_, 0, v___x_2846_);
    return v___x_2847_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0___boxed(
    mut v_msgData_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msgData_2848_, v___y_2849_, v___y_2850_);
    leanh::lean_dec(v___y_2850_);
    leanh::lean_dec_ref(v___y_2849_);
    return v_res_2852_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(
    mut v_oldTraces_2853_: *mut leanh::LeanObject,
    mut v_data_2854_: *mut leanh::LeanObject,
    mut v_ref_2855_: *mut leanh::LeanObject,
    mut v_msg_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2872_: u8 = 0;
    let mut v_cancelTk_x3f_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2874_: u8 = 0;
    let mut v_inheritedTraceOptions_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2882_: usize = 0;
    let mut v___x_2883_: usize = 0;
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v_tid_2904_: u64 = 0;
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2923_: u8 = 0;
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2860_ = leanh::lean_ctor_get(v___y_2857_, 0);
                v_fileMap_2861_ = leanh::lean_ctor_get(v___y_2857_, 1);
                v_options_2862_ = leanh::lean_ctor_get(v___y_2857_, 2);
                v_currRecDepth_2863_ = leanh::lean_ctor_get(v___y_2857_, 3);
                v_maxRecDepth_2864_ = leanh::lean_ctor_get(v___y_2857_, 4);
                v_ref_2865_ = leanh::lean_ctor_get(v___y_2857_, 5);
                v_currNamespace_2866_ = leanh::lean_ctor_get(v___y_2857_, 6);
                v_openDecls_2867_ = leanh::lean_ctor_get(v___y_2857_, 7);
                v_initHeartbeats_2868_ = leanh::lean_ctor_get(v___y_2857_, 8);
                v_maxHeartbeats_2869_ = leanh::lean_ctor_get(v___y_2857_, 9);
                v_quotContext_2870_ = leanh::lean_ctor_get(v___y_2857_, 10);
                v_currMacroScope_2871_ = leanh::lean_ctor_get(v___y_2857_, 11);
                v_diag_2872_ = leanh::lean_ctor_get_uint8(
                    v___y_2857_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2873_ = leanh::lean_ctor_get(v___y_2857_, 12);
                v_suppressElabErrors_2874_ = leanh::lean_ctor_get_uint8(
                    v___y_2857_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2875_ = leanh::lean_ctor_get(v___y_2857_, 13);
                v___x_2876_ = lean_st_ref_get(v___y_2858_);
                v_traceState_2877_ = leanh::lean_ctor_get(v___x_2876_, 4);
                leanh::lean_inc_ref(v_traceState_2877_);
                leanh::lean_dec(v___x_2876_);
                v_traces_2878_ = leanh::lean_ctor_get(v_traceState_2877_, 0);
                leanh::lean_inc_ref(v_traces_2878_);
                leanh::lean_dec_ref(v_traceState_2877_);
                v_ref_2879_ = l_Lean_replaceRef(v_ref_2855_, v_ref_2865_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2875_);
                leanh::lean_inc(v_cancelTk_x3f_2873_);
                leanh::lean_inc(v_currMacroScope_2871_);
                leanh::lean_inc(v_quotContext_2870_);
                leanh::lean_inc(v_maxHeartbeats_2869_);
                leanh::lean_inc(v_initHeartbeats_2868_);
                leanh::lean_inc(v_openDecls_2867_);
                leanh::lean_inc(v_currNamespace_2866_);
                leanh::lean_inc(v_maxRecDepth_2864_);
                leanh::lean_inc(v_currRecDepth_2863_);
                leanh::lean_inc_ref(v_options_2862_);
                leanh::lean_inc_ref(v_fileMap_2861_);
                leanh::lean_inc_ref(v_fileName_2860_);
                v___x_2880_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2880_, 0, v_fileName_2860_);
                leanh::lean_ctor_set(v___x_2880_, 1, v_fileMap_2861_);
                leanh::lean_ctor_set(v___x_2880_, 2, v_options_2862_);
                leanh::lean_ctor_set(v___x_2880_, 3, v_currRecDepth_2863_);
                leanh::lean_ctor_set(v___x_2880_, 4, v_maxRecDepth_2864_);
                leanh::lean_ctor_set(v___x_2880_, 5, v_ref_2879_);
                leanh::lean_ctor_set(v___x_2880_, 6, v_currNamespace_2866_);
                leanh::lean_ctor_set(v___x_2880_, 7, v_openDecls_2867_);
                leanh::lean_ctor_set(v___x_2880_, 8, v_initHeartbeats_2868_);
                leanh::lean_ctor_set(v___x_2880_, 9, v_maxHeartbeats_2869_);
                leanh::lean_ctor_set(v___x_2880_, 10, v_quotContext_2870_);
                leanh::lean_ctor_set(v___x_2880_, 11, v_currMacroScope_2871_);
                leanh::lean_ctor_set(v___x_2880_, 12, v_cancelTk_x3f_2873_);
                leanh::lean_ctor_set(v___x_2880_, 13, v_inheritedTraceOptions_2875_);
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_2872_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2880_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2874_,
                );
                v___x_2881_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2878_);
                leanh::lean_dec_ref(v_traces_2878_);
                v_sz_2882_ = lean_array_size(v___x_2881_);
                v___x_2883_ = 0usize;
                v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5_spec__7(v_sz_2882_, v___x_2883_, v___x_2881_);
                v_msg_2885_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_2885_, 0, v_data_2854_);
                leanh::lean_ctor_set(v_msg_2885_, 1, v_msg_2856_);
                leanh::lean_ctor_set(v_msg_2885_, 2, v___x_2884_);
                v___x_2886_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_2885_, v___x_2880_, v___y_2858_);
                leanh::lean_dec_ref_known(v___x_2880_, 14);
                v_a_2887_ = leanh::lean_ctor_get(v___x_2886_, 0);
                v_isSharedCheck_2924_ = (!leanh::lean_is_exclusive(v___x_2886_)) as u8;
                if v_isSharedCheck_2924_ == 0 {
                    v___x_2889_ = v___x_2886_;
                    v_isShared_2890_ = v_isSharedCheck_2924_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2887_);
                    leanh::lean_dec(v___x_2886_);
                    v___x_2889_ = leanh::lean_box(0);
                    v_isShared_2890_ = v_isSharedCheck_2924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2891_ = lean_st_ref_take(v___y_2858_);
                v_traceState_2892_ = leanh::lean_ctor_get(v___x_2891_, 4);
                v_env_2893_ = leanh::lean_ctor_get(v___x_2891_, 0);
                v_nextMacroScope_2894_ = leanh::lean_ctor_get(v___x_2891_, 1);
                v_ngen_2895_ = leanh::lean_ctor_get(v___x_2891_, 2);
                v_auxDeclNGen_2896_ = leanh::lean_ctor_get(v___x_2891_, 3);
                v_cache_2897_ = leanh::lean_ctor_get(v___x_2891_, 5);
                v_messages_2898_ = leanh::lean_ctor_get(v___x_2891_, 6);
                v_infoState_2899_ = leanh::lean_ctor_get(v___x_2891_, 7);
                v_snapshotTasks_2900_ = leanh::lean_ctor_get(v___x_2891_, 8);
                v_isSharedCheck_2923_ = (!leanh::lean_is_exclusive(v___x_2891_)) as u8;
                if v_isSharedCheck_2923_ == 0 {
                    v___x_2902_ = v___x_2891_;
                    v_isShared_2903_ = v_isSharedCheck_2923_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2900_);
                    leanh::lean_inc(v_infoState_2899_);
                    leanh::lean_inc(v_messages_2898_);
                    leanh::lean_inc(v_cache_2897_);
                    leanh::lean_inc(v_traceState_2892_);
                    leanh::lean_inc(v_auxDeclNGen_2896_);
                    leanh::lean_inc(v_ngen_2895_);
                    leanh::lean_inc(v_nextMacroScope_2894_);
                    leanh::lean_inc(v_env_2893_);
                    leanh::lean_dec(v___x_2891_);
                    v___x_2902_ = leanh::lean_box(0);
                    v_isShared_2903_ = v_isSharedCheck_2923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2904_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2892_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2921_ =
                    (!leanh::lean_is_exclusive(v_traceState_2892_)) as u8;
                if v_isSharedCheck_2921_ == 0 {
                    v_unused_2922_ = leanh::lean_ctor_get(v_traceState_2892_, 0);
                    leanh::lean_dec(v_unused_2922_);
                    v___x_2906_ = v_traceState_2892_;
                    v_isShared_2907_ = v_isSharedCheck_2921_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_2892_);
                    v___x_2906_ = leanh::lean_box(0);
                    v_isShared_2907_ = v_isSharedCheck_2921_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2908_, 0, v_ref_2855_);
                leanh::lean_ctor_set(v___x_2908_, 1, v_a_2887_);
                v___x_2909_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2853_, v___x_2908_);
                if v_isShared_2907_ == 0 {
                    leanh::lean_ctor_set(v___x_2906_, 0, v___x_2909_);
                    v___x_2911_ = v___x_2906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2920_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2909_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2920_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2904_,
                    );
                    v___x_2911_ = v_reuseFailAlloc_2920_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2903_ == 0 {
                    leanh::lean_ctor_set(v___x_2902_, 4, v___x_2911_);
                    v___x_2913_ = v___x_2902_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_env_2893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_nextMacroScope_2894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_ngen_2895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_auxDeclNGen_2896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 4, v___x_2911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 5, v_cache_2897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 6, v_messages_2898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 7, v_infoState_2899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 8, v_snapshotTasks_2900_);
                    v___x_2913_ = v_reuseFailAlloc_2919_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2914_ = lean_st_ref_set(v___y_2858_, v___x_2913_);
                v___x_2915_ = leanh::lean_box(0);
                if v_isShared_2890_ == 0 {
                    leanh::lean_ctor_set(v___x_2889_, 0, v___x_2915_);
                    v___x_2917_ = v___x_2889_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5___boxed(
    mut v_oldTraces_2925_: *mut leanh::LeanObject,
    mut v_data_2926_: *mut leanh::LeanObject,
    mut v_ref_2927_: *mut leanh::LeanObject,
    mut v_msg_2928_: *mut leanh::LeanObject,
    mut v___y_2929_: *mut leanh::LeanObject,
    mut v___y_2930_: *mut leanh::LeanObject,
    mut v___y_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_2925_, v_data_2926_, v_ref_2927_, v_msg_2928_, v___y_2929_, v___y_2930_);
    leanh::lean_dec(v___y_2930_);
    leanh::lean_dec_ref(v___y_2929_);
    return v_res_2932_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(
    mut v_x_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_a_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2946_: u8 = 0;
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2933_) == 0 {
                    v_a_2935_ = leanh::lean_ctor_get(v_x_2933_, 0);
                    v_isSharedCheck_2942_ = (!leanh::lean_is_exclusive(v_x_2933_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v_x_2933_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2935_);
                        leanh::lean_dec(v_x_2933_);
                        v___x_2937_ = leanh::lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2943_ = leanh::lean_ctor_get(v_x_2933_, 0);
                    v_isSharedCheck_2950_ = (!leanh::lean_is_exclusive(v_x_2933_)) as u8;
                    if v_isSharedCheck_2950_ == 0 {
                        v___x_2945_ = v_x_2933_;
                        v_isShared_2946_ = v_isSharedCheck_2950_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2943_);
                        leanh::lean_dec(v_x_2933_);
                        v___x_2945_ = leanh::lean_box(0);
                        v_isShared_2946_ = v_isSharedCheck_2950_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2938_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2937_, 1);
                    v___x_2940_ = v___x_2937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2940_;
            }
            3 => {
                if v_isShared_2946_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2945_, 0);
                    v___x_2948_ = v___x_2945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
                    v___x_2948_ = v_reuseFailAlloc_2949_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2948_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg___boxed(
    mut v_x_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_x_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(
    mut v_e_2954_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_2954_) == 0 {
        let mut v___x_2955_: u8 = 0;
        v___x_2955_ = 2;
        return v___x_2955_;
    } else {
        let mut v___x_2956_: u8 = 0;
        v___x_2956_ = 0;
        return v___x_2956_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4___boxed(
    mut v_e_2957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2958_: u8 = 0;
    let mut v_r_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2958_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_e_2957_);
    leanh::lean_dec_ref(v_e_2957_);
    v_r_2959_ = leanh::lean_box((v_res_2958_) as usize);
    return v_r_2959_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(
    mut v_opts_2960_: *mut leanh::LeanObject,
    mut v_opt_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2962_ = leanh::lean_ctor_get(v_opt_2961_, 0);
    v_defValue_2963_ = leanh::lean_ctor_get(v_opt_2961_, 1);
    v_map_2964_ = leanh::lean_ctor_get(v_opts_2960_, 0);
    v___x_2965_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2964_,
            v_name_2962_,
        );
    if leanh::lean_obj_tag(v___x_2965_) == 0 {
        leanh::lean_inc(v_defValue_2963_);
        return v_defValue_2963_;
    } else {
        let mut v_val_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2966_ = leanh::lean_ctor_get(v___x_2965_, 0);
        leanh::lean_inc(v_val_2966_);
        leanh::lean_dec_ref_known(v___x_2965_, 1);
        if leanh::lean_obj_tag(v_val_2966_) == 3 {
            let mut v_v_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2967_ = leanh::lean_ctor_get(v_val_2966_, 0);
            leanh::lean_inc(v_v_2967_);
            leanh::lean_dec_ref_known(v_val_2966_, 1);
            return v_v_2967_;
        } else {
            leanh::lean_dec(v_val_2966_);
            leanh::lean_inc(v_defValue_2963_);
            return v_defValue_2963_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7___boxed(
    mut v_opts_2968_: *mut leanh::LeanObject,
    mut v_opt_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2970_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_2968_, v_opt_2969_);
    leanh::lean_dec_ref(v_opt_2969_);
    leanh::lean_dec_ref(v_opts_2968_);
    return v_res_2970_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__0;
    v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2()
-> f64 {
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: f64 = 0.0;
    v___x_2974_ = leanh::lean_unsigned_to_nat(0);
    v___x_2975_ = lean_float_of_nat(v___x_2974_);
    return v___x_2975_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__3;
    v___x_2978_ = l_Lean_stringToMessageData(v___x_2977_);
    return v___x_2978_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5()
-> f64 {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: f64 = 0.0;
    v___x_2979_ = leanh::lean_unsigned_to_nat(1000);
    v___x_2980_ = lean_float_of_nat(v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(
    mut v_cls_2981_: *mut leanh::LeanObject,
    mut v_collapsed_2982_: u8,
    mut v_tag_2983_: *mut leanh::LeanObject,
    mut v_opts_2984_: *mut leanh::LeanObject,
    mut v_clsEnabled_2985_: u8,
    mut v_oldTraces_2986_: *mut leanh::LeanObject,
    mut v_msg_2987_: *mut leanh::LeanObject,
    mut v_resStartStop_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
    mut v___y_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___y_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v_fst_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: u8 = 0;
    let mut v___y_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3021_: u8 = 0;
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: f64 = 0.0;
    let mut v_data_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: f64 = 0.0;
    let mut v___x_3035_: f64 = 0.0;
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3044_: u8 = 0;
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3057_: u8 = 0;
    let mut v_tid_3058_: u64 = 0;
    let mut v_traces_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_isSharedCheck_3073_: u8 = 0;
    let mut v___y_3075_: f64 = 0.0;
    let mut v___x_3076_: f64 = 0.0;
    let mut v___x_3077_: f64 = 0.0;
    let mut v___x_3078_: f64 = 0.0;
    let mut v___x_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: f64 = 0.0;
    let mut v___x_3085_: f64 = 0.0;
    let mut v___x_3086_: f64 = 0.0;
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: f64 = 0.0;
    let mut v_isSharedCheck_3090_: u8 = 0;
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2992_ = leanh::lean_ctor_get(v_resStartStop_2988_, 0);
                v_snd_2993_ = leanh::lean_ctor_get(v_resStartStop_2988_, 1);
                v_isSharedCheck_3091_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_2988_)) as u8;
                if v_isSharedCheck_3091_ == 0 {
                    v___x_2995_ = v_resStartStop_2988_;
                    v_isShared_2996_ = v_isSharedCheck_3091_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2993_);
                    leanh::lean_inc(v_fst_2992_);
                    leanh::lean_dec(v_resStartStop_2988_);
                    v___x_2995_ = leanh::lean_box(0);
                    v_isShared_2996_ = v_isSharedCheck_3091_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3011_ = leanh::lean_ctor_get(v_snd_2993_, 0);
                v_snd_3012_ = leanh::lean_ctor_get(v_snd_2993_, 1);
                v_isSharedCheck_3090_ = (!leanh::lean_is_exclusive(v_snd_2993_)) as u8;
                if v_isSharedCheck_3090_ == 0 {
                    v___x_3014_ = v_snd_2993_;
                    v_isShared_3015_ = v_isSharedCheck_3090_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3012_);
                    leanh::lean_inc(v_fst_3011_);
                    leanh::lean_dec(v_snd_2993_);
                    v___x_3014_ = leanh::lean_box(0);
                    v_isShared_3015_ = v_isSharedCheck_3090_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_2998_);
                v___x_3001_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_2986_, v_data_3000_, v___y_2998_, v___y_2999_, v___y_2989_, v___y_2990_);
                if leanh::lean_obj_tag(v___x_3001_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3001_, 1);
                    v___x_3002_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_2992_);
                    return v___x_3002_;
                } else {
                    leanh::lean_dec(v_fst_2992_);
                    v_a_3003_ = leanh::lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3010_ = (!leanh::lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3010_ == 0 {
                        v___x_3005_ = v___x_3001_;
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3003_);
                        leanh::lean_dec(v___x_3001_);
                        v___x_3005_ = leanh::lean_box(0);
                        v_isShared_3006_ = v_isSharedCheck_3010_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3006_ == 0 {
                    v___x_3008_ = v___x_3005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
                    v___x_3008_ = v_reuseFailAlloc_3009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3008_;
            }
            5 => {
                v___x_3016_ = l_Lean_trace_profiler;
                v___x_3017_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_opts_2984_,
                        v___x_3016_,
                    );
                if v___x_3017_ == 0 {
                    v___y_3044_ = v___x_3017_;
                    state = 10;
                    continue;
                } else {
                    v___x_3080_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3081_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                            v_opts_2984_,
                            v___x_3080_,
                        );
                    if v___x_3081_ == 0 {
                        v___x_3082_ = l_Lean_trace_profiler_threshold;
                        v___x_3083_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_2984_, v___x_3082_);
                        v___x_3084_ = lean_float_of_nat(v___x_3083_);
                        v___x_3085_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
                        v___x_3086_ = lean_float_div(v___x_3084_, v___x_3085_);
                        v___y_3075_ = v___x_3086_;
                        state = 15;
                        continue;
                    } else {
                        v___x_3087_ = l_Lean_trace_profiler_threshold;
                        v___x_3088_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_2984_, v___x_3087_);
                        v___x_3089_ = lean_float_of_nat(v___x_3088_);
                        v___y_3075_ = v___x_3089_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_3021_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__4(v_fst_2992_);
                v___x_3022_ = l_Lean_TraceResult_toEmoji(v_result_3021_);
                v___x_3023_ = l_Lean_stringToMessageData(v___x_3022_);
                v___x_3024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
                if v_isShared_3015_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3014_, 7);
                    leanh::lean_ctor_set(v___x_3014_, 1, v___x_3024_);
                    leanh::lean_ctor_set(v___x_3014_, 0, v___x_3023_);
                    v___x_3026_ = v___x_3014_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3024_);
                    v___x_3026_ = v_reuseFailAlloc_3037_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2996_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2995_, 7);
                    leanh::lean_ctor_set(v___x_2995_, 1, v_a_3020_);
                    leanh::lean_ctor_set(v___x_2995_, 0, v___x_3026_);
                    v_m_3028_ = v___x_2995_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3020_);
                    v_m_3028_ = v_reuseFailAlloc_3036_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3029_ = leanh::lean_box((v_result_3021_) as usize);
                v___x_3030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3030_, 0, v___x_3029_);
                v___x_3031_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
                leanh::lean_inc_ref(v_tag_2983_);
                leanh::lean_inc_ref(v___x_3030_);
                leanh::lean_inc(v_cls_2981_);
                v_data_3032_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_3032_, 0, v_cls_2981_);
                leanh::lean_ctor_set(v_data_3032_, 1, v___x_3030_);
                leanh::lean_ctor_set(v_data_3032_, 2, v_tag_2983_);
                leanh::lean_ctor_set_float(
                    v_data_3032_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3031_,
                );
                leanh::lean_ctor_set_float(
                    v_data_3032_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3031_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_3032_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_2982_,
                );
                if v___x_3017_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3030_, 1);
                    leanh::lean_dec(v_snd_3012_);
                    leanh::lean_dec(v_fst_3011_);
                    leanh::lean_dec_ref(v_tag_2983_);
                    leanh::lean_dec(v_cls_2981_);
                    v___y_2998_ = v___y_3019_;
                    v___y_2999_ = v_m_3028_;
                    v_data_3000_ = v_data_3032_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_3032_, 3);
                    v_data_3033_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_3033_, 0, v_cls_2981_);
                    leanh::lean_ctor_set(v_data_3033_, 1, v___x_3030_);
                    leanh::lean_ctor_set(v_data_3033_, 2, v_tag_2983_);
                    v___x_3034_ = leanh::lean_unbox_float(v_fst_3011_);
                    leanh::lean_dec(v_fst_3011_);
                    leanh::lean_ctor_set_float(
                        v_data_3033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_3034_,
                    );
                    v___x_3035_ = leanh::lean_unbox_float(v_snd_3012_);
                    leanh::lean_dec(v_snd_3012_);
                    leanh::lean_ctor_set_float(
                        v_data_3033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_3035_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_3033_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_2982_,
                    );
                    v___y_2998_ = v___y_3019_;
                    v___y_2999_ = v_m_3028_;
                    v_data_3000_ = v_data_3033_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_3039_ = leanh::lean_ctor_get(v___y_2989_, 5);
                leanh::lean_inc(v___y_2990_);
                leanh::lean_inc_ref(v___y_2989_);
                leanh::lean_inc(v_fst_2992_);
                v___x_3040_ = leanh::lean_apply_4(
                    v_msg_2987_,
                    v_fst_2992_,
                    v___y_2989_,
                    v___y_2990_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3040_) == 0 {
                    v_a_3041_ = leanh::lean_ctor_get(v___x_3040_, 0);
                    leanh::lean_inc(v_a_3041_);
                    leanh::lean_dec_ref_known(v___x_3040_, 1);
                    v___y_3019_ = v_ref_3039_;
                    v_a_3020_ = v_a_3041_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_3040_, 1);
                    v___x_3042_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
                    v___y_3019_ = v_ref_3039_;
                    v_a_3020_ = v___x_3042_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_2985_ == 0 {
                    if v___y_3044_ == 0 {
                        leanh::lean_del_object(v___x_3014_);
                        leanh::lean_dec(v_snd_3012_);
                        leanh::lean_dec(v_fst_3011_);
                        leanh::lean_del_object(v___x_2995_);
                        leanh::lean_dec_ref(v_msg_2987_);
                        leanh::lean_dec_ref(v_tag_2983_);
                        leanh::lean_dec(v_cls_2981_);
                        v___x_3045_ = lean_st_ref_take(v___y_2990_);
                        v_traceState_3046_ = leanh::lean_ctor_get(v___x_3045_, 4);
                        v_env_3047_ = leanh::lean_ctor_get(v___x_3045_, 0);
                        v_nextMacroScope_3048_ = leanh::lean_ctor_get(v___x_3045_, 1);
                        v_ngen_3049_ = leanh::lean_ctor_get(v___x_3045_, 2);
                        v_auxDeclNGen_3050_ = leanh::lean_ctor_get(v___x_3045_, 3);
                        v_cache_3051_ = leanh::lean_ctor_get(v___x_3045_, 5);
                        v_messages_3052_ = leanh::lean_ctor_get(v___x_3045_, 6);
                        v_infoState_3053_ = leanh::lean_ctor_get(v___x_3045_, 7);
                        v_snapshotTasks_3054_ = leanh::lean_ctor_get(v___x_3045_, 8);
                        v_isSharedCheck_3073_ =
                            (!leanh::lean_is_exclusive(v___x_3045_)) as u8;
                        if v_isSharedCheck_3073_ == 0 {
                            v___x_3056_ = v___x_3045_;
                            v_isShared_3057_ = v_isSharedCheck_3073_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_3054_);
                            leanh::lean_inc(v_infoState_3053_);
                            leanh::lean_inc(v_messages_3052_);
                            leanh::lean_inc(v_cache_3051_);
                            leanh::lean_inc(v_traceState_3046_);
                            leanh::lean_inc(v_auxDeclNGen_3050_);
                            leanh::lean_inc(v_ngen_3049_);
                            leanh::lean_inc(v_nextMacroScope_3048_);
                            leanh::lean_inc(v_env_3047_);
                            leanh::lean_dec(v___x_3045_);
                            v___x_3056_ = leanh::lean_box(0);
                            v_isShared_3057_ = v_isSharedCheck_3073_;
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
                v_tid_3058_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3046_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3059_ = leanh::lean_ctor_get(v_traceState_3046_, 0);
                v_isSharedCheck_3072_ =
                    (!leanh::lean_is_exclusive(v_traceState_3046_)) as u8;
                if v_isSharedCheck_3072_ == 0 {
                    v___x_3061_ = v_traceState_3046_;
                    v_isShared_3062_ = v_isSharedCheck_3072_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3059_);
                    leanh::lean_dec(v_traceState_3046_);
                    v___x_3061_ = leanh::lean_box(0);
                    v_isShared_3062_ = v_isSharedCheck_3072_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3063_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_2986_, v_traces_3059_);
                leanh::lean_dec_ref(v_traces_3059_);
                if v_isShared_3062_ == 0 {
                    leanh::lean_ctor_set(v___x_3061_, 0, v___x_3063_);
                    v___x_3065_ = v___x_3061_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3063_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3071_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3058_,
                    );
                    v___x_3065_ = v_reuseFailAlloc_3071_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3057_ == 0 {
                    leanh::lean_ctor_set(v___x_3056_, 4, v___x_3065_);
                    v___x_3067_ = v___x_3056_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_env_3047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_nextMacroScope_3048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_ngen_3049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_auxDeclNGen_3050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 4, v___x_3065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 5, v_cache_3051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 6, v_messages_3052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 7, v_infoState_3053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 8, v_snapshotTasks_3054_);
                    v___x_3067_ = v_reuseFailAlloc_3070_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3068_ = lean_st_ref_set(v___y_2990_, v___x_3067_);
                v___x_3069_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_2992_);
                return v___x_3069_;
            }
            15 => {
                v___x_3076_ = leanh::lean_unbox_float(v_snd_3012_);
                v___x_3077_ = leanh::lean_unbox_float(v_fst_3011_);
                v___x_3078_ = lean_float_sub(v___x_3076_, v___x_3077_);
                v___x_3079_ = lean_float_decLt(v___y_3075_, v___x_3078_);
                v___y_3044_ = v___x_3079_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___boxed(
    mut v_cls_3092_: *mut leanh::LeanObject,
    mut v_collapsed_3093_: *mut leanh::LeanObject,
    mut v_tag_3094_: *mut leanh::LeanObject,
    mut v_opts_3095_: *mut leanh::LeanObject,
    mut v_clsEnabled_3096_: *mut leanh::LeanObject,
    mut v_oldTraces_3097_: *mut leanh::LeanObject,
    mut v_msg_3098_: *mut leanh::LeanObject,
    mut v_resStartStop_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
    mut v___y_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_3103_: u8 = 0;
    let mut v_clsEnabled_boxed_3104_: u8 = 0;
    let mut v_res_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3103_ = (leanh::lean_unbox(v_collapsed_3093_) as u8);
    v_clsEnabled_boxed_3104_ = (leanh::lean_unbox(v_clsEnabled_3096_) as u8);
    v_res_3105_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v_cls_3092_, v_collapsed_boxed_3103_, v_tag_3094_, v_opts_3095_, v_clsEnabled_boxed_3104_, v_oldTraces_3097_, v_msg_3098_, v_resStartStop_3099_, v___y_3100_, v___y_3101_);
    leanh::lean_dec(v___y_3101_);
    leanh::lean_dec_ref(v___y_3100_);
    leanh::lean_dec_ref(v_opts_3095_);
    return v_res_3105_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(
    mut v_msg_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3110_ = leanh::lean_ctor_get(v___y_3107_, 5);
                v___x_3111_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_3106_, v___y_3107_, v___y_3108_);
                v_a_3112_ = leanh::lean_ctor_get(v___x_3111_, 0);
                v_isSharedCheck_3120_ = (!leanh::lean_is_exclusive(v___x_3111_)) as u8;
                if v_isSharedCheck_3120_ == 0 {
                    v___x_3114_ = v___x_3111_;
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3112_);
                    leanh::lean_dec(v___x_3111_);
                    v___x_3114_ = leanh::lean_box(0);
                    v_isShared_3115_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3110_);
                v___x_3116_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3116_, 0, v_ref_3110_);
                leanh::lean_ctor_set(v___x_3116_, 1, v_a_3112_);
                if v_isShared_3115_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3114_, 1);
                    leanh::lean_ctor_set(v___x_3114_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
                    v___x_3118_ = v_reuseFailAlloc_3119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg___boxed(
    mut v_msg_3121_: *mut leanh::LeanObject,
    mut v___y_3122_: *mut leanh::LeanObject,
    mut v___y_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(
            v_msg_3121_,
            v___y_3122_,
            v___y_3123_,
        );
    leanh::lean_dec(v___y_3123_);
    leanh::lean_dec_ref(v___y_3122_);
    return v_res_3125_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(
    mut v_cls_3129_: *mut leanh::LeanObject,
    mut v_msg_3130_: *mut leanh::LeanObject,
    mut v___y_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v_tid_3153_: u64 = 0;
    let mut v_traces_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: f64 = 0.0;
    let mut v___x_3160_: u8 = 0;
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3134_ = leanh::lean_ctor_get(v___y_3131_, 5);
                v___x_3135_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0_spec__0(v_msg_3130_, v___y_3131_, v___y_3132_);
                v_a_3136_ = leanh::lean_ctor_get(v___x_3135_, 0);
                v_isSharedCheck_3180_ = (!leanh::lean_is_exclusive(v___x_3135_)) as u8;
                if v_isSharedCheck_3180_ == 0 {
                    v___x_3138_ = v___x_3135_;
                    v_isShared_3139_ = v_isSharedCheck_3180_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3136_);
                    leanh::lean_dec(v___x_3135_);
                    v___x_3138_ = leanh::lean_box(0);
                    v_isShared_3139_ = v_isSharedCheck_3180_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3140_ = lean_st_ref_take(v___y_3132_);
                v_traceState_3141_ = leanh::lean_ctor_get(v___x_3140_, 4);
                v_env_3142_ = leanh::lean_ctor_get(v___x_3140_, 0);
                v_nextMacroScope_3143_ = leanh::lean_ctor_get(v___x_3140_, 1);
                v_ngen_3144_ = leanh::lean_ctor_get(v___x_3140_, 2);
                v_auxDeclNGen_3145_ = leanh::lean_ctor_get(v___x_3140_, 3);
                v_cache_3146_ = leanh::lean_ctor_get(v___x_3140_, 5);
                v_messages_3147_ = leanh::lean_ctor_get(v___x_3140_, 6);
                v_infoState_3148_ = leanh::lean_ctor_get(v___x_3140_, 7);
                v_snapshotTasks_3149_ = leanh::lean_ctor_get(v___x_3140_, 8);
                v_isSharedCheck_3179_ = (!leanh::lean_is_exclusive(v___x_3140_)) as u8;
                if v_isSharedCheck_3179_ == 0 {
                    v___x_3151_ = v___x_3140_;
                    v_isShared_3152_ = v_isSharedCheck_3179_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3149_);
                    leanh::lean_inc(v_infoState_3148_);
                    leanh::lean_inc(v_messages_3147_);
                    leanh::lean_inc(v_cache_3146_);
                    leanh::lean_inc(v_traceState_3141_);
                    leanh::lean_inc(v_auxDeclNGen_3145_);
                    leanh::lean_inc(v_ngen_3144_);
                    leanh::lean_inc(v_nextMacroScope_3143_);
                    leanh::lean_inc(v_env_3142_);
                    leanh::lean_dec(v___x_3140_);
                    v___x_3151_ = leanh::lean_box(0);
                    v_isShared_3152_ = v_isSharedCheck_3179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3153_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3141_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3154_ = leanh::lean_ctor_get(v_traceState_3141_, 0);
                v_isSharedCheck_3178_ =
                    (!leanh::lean_is_exclusive(v_traceState_3141_)) as u8;
                if v_isSharedCheck_3178_ == 0 {
                    v___x_3156_ = v_traceState_3141_;
                    v_isShared_3157_ = v_isSharedCheck_3178_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3154_);
                    leanh::lean_dec(v_traceState_3141_);
                    v___x_3156_ = leanh::lean_box(0);
                    v_isShared_3157_ = v_isSharedCheck_3178_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3158_ = leanh::lean_box(0);
                v___x_3159_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
                v___x_3160_ = 0;
                v___x_3161_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0;
                v___x_3162_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_3162_, 0, v_cls_3129_);
                leanh::lean_ctor_set(v___x_3162_, 1, v___x_3158_);
                leanh::lean_ctor_set(v___x_3162_, 2, v___x_3161_);
                leanh::lean_ctor_set_float(
                    v___x_3162_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3159_,
                );
                leanh::lean_ctor_set_float(
                    v___x_3162_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3159_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3162_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3160_,
                );
                v___x_3163_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__1;
                v___x_3164_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3164_, 0, v___x_3162_);
                leanh::lean_ctor_set(v___x_3164_, 1, v_a_3136_);
                leanh::lean_ctor_set(v___x_3164_, 2, v___x_3163_);
                leanh::lean_inc(v_ref_3134_);
                v___x_3165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3165_, 0, v_ref_3134_);
                leanh::lean_ctor_set(v___x_3165_, 1, v___x_3164_);
                v___x_3166_ = l_Lean_PersistentArray_push___redArg(v_traces_3154_, v___x_3165_);
                if v_isShared_3157_ == 0 {
                    leanh::lean_ctor_set(v___x_3156_, 0, v___x_3166_);
                    v___x_3168_ = v___x_3156_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3166_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3177_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3153_,
                    );
                    v___x_3168_ = v_reuseFailAlloc_3177_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3152_ == 0 {
                    leanh::lean_ctor_set(v___x_3151_, 4, v___x_3168_);
                    v___x_3170_ = v___x_3151_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_env_3142_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_nextMacroScope_3143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_ngen_3144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 3, v_auxDeclNGen_3145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 4, v___x_3168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 5, v_cache_3146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 6, v_messages_3147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 7, v_infoState_3148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 8, v_snapshotTasks_3149_);
                    v___x_3170_ = v_reuseFailAlloc_3176_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3171_ = lean_st_ref_set(v___y_3132_, v___x_3170_);
                v___x_3172_ = leanh::lean_box(0);
                if v_isShared_3139_ == 0 {
                    leanh::lean_ctor_set(v___x_3138_, 0, v___x_3172_);
                    v___x_3174_ = v___x_3138_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___boxed(
    mut v_cls_3181_: *mut leanh::LeanObject,
    mut v_msg_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3186_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(
        v_cls_3181_,
        v_msg_3182_,
        v___y_3183_,
        v___y_3184_,
    );
    leanh::lean_dec(v___y_3184_);
    leanh::lean_dec_ref(v___y_3183_);
    return v_res_3186_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3197_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3;
    v___x_3198_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__5;
    v___x_3199_ = l_Lean_Name_append(v___x_3198_, v___x_3197_);
    return v___x_3199_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9() -> f64 {
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: f64 = 0.0;
    v___x_3202_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_3203_ = lean_float_of_nat(v___x_3202_);
    return v___x_3203_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__11;
    v___x_3207_ = l_Lean_stringToMessageData(v___x_3206_);
    return v___x_3207_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load(
    mut v_lratPath_3209_: *mut leanh::LeanObject,
    mut v_trimProofs_3210_: u8,
    mut v_a_3211_: *mut leanh::LeanObject,
    mut v_a_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v_ref_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3222_: u8 = 0;
    let mut v___f_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_unused_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_proof_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3267_: u8 = 0;
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: u8 = 0;
    let mut v___y_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: f64 = 0.0;
    let mut v___x_3287_: f64 = 0.0;
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3295_: u8 = 0;
    let mut v___y_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: u8 = 0;
    let mut v___y_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: f64 = 0.0;
    let mut v___x_3312_: f64 = 0.0;
    let mut v___x_3313_: f64 = 0.0;
    let mut v___x_3314_: f64 = 0.0;
    let mut v___x_3315_: f64 = 0.0;
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: u8 = 0;
    let mut v___y_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3333_: u8 = 0;
    let mut v___y_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_a_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_a_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3386_: u8 = 0;
    let mut v_a_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v_a_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut v___y_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3415_: u8 = 0;
    let mut v_ref_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3423_: u8 = 0;
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3427_: u8 = 0;
    let mut v_a_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut v_a_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3451_: u8 = 0;
    let mut v_ref_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: u8 = 0;
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut v_a_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_a_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3507_: u8 = 0;
    let mut v___y_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v___f_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___y_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: f64 = 0.0;
    let mut v___x_3540_: f64 = 0.0;
    let mut v___x_3541_: f64 = 0.0;
    let mut v___x_3542_: f64 = 0.0;
    let mut v___x_3543_: f64 = 0.0;
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: f64 = 0.0;
    let mut v___x_3565_: f64 = 0.0;
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_a_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v_ref_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3214_ = l_IO_FS_readBinFile(v_lratPath_3209_);
                if leanh::lean_obj_tag(v___x_3214_) == 0 {
                    v_options_3215_ = leanh::lean_ctor_get(v_a_3211_, 2);
                    v_a_3216_ = leanh::lean_ctor_get(v___x_3214_, 0);
                    v_isSharedCheck_3650_ = (!leanh::lean_is_exclusive(v___x_3214_)) as u8;
                    if v_isSharedCheck_3650_ == 0 {
                        v___x_3218_ = v___x_3214_;
                        v_isShared_3219_ = v_isSharedCheck_3650_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3216_);
                        leanh::lean_dec(v___x_3214_);
                        v___x_3218_ = leanh::lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3651_ = leanh::lean_ctor_get(v___x_3214_, 0);
                    v_isSharedCheck_3663_ = (!leanh::lean_is_exclusive(v___x_3214_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v___x_3653_ = v___x_3214_;
                        v_isShared_3654_ = v_isSharedCheck_3663_;
                        state = 57;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3651_);
                        leanh::lean_dec(v___x_3214_);
                        v___x_3653_ = leanh::lean_box(0);
                        v_isShared_3654_ = v_isSharedCheck_3663_;
                        state = 57;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_3220_ = leanh::lean_ctor_get(v_a_3211_, 5);
                v_inheritedTraceOptions_3221_ = leanh::lean_ctor_get(v_a_3211_, 13);
                v_hasTrace_3222_ = leanh::lean_ctor_get_uint8(
                    v_options_3215_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___f_3223_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__0;
                v___f_3224_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3224_, 0, v_a_3216_);
                v___x_3225_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3;
                v___x_3275_ = 1;
                v___x_3276_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0;
                if v_hasTrace_3222_ == 0 {
                    v___x_3511_ = l_IO_lazyPure___redArg(v___f_3224_);
                    if leanh::lean_obj_tag(v___x_3511_) == 0 {
                        v_a_3512_ = leanh::lean_ctor_get(v___x_3511_, 0);
                        leanh::lean_inc(v_a_3512_);
                        leanh::lean_dec_ref_known(v___x_3511_, 1);
                        if leanh::lean_obj_tag(v_a_3512_) == 0 {
                            v_a_3513_ = leanh::lean_ctor_get(v_a_3512_, 0);
                            leanh::lean_inc(v_a_3513_);
                            leanh::lean_dec_ref_known(v_a_3512_, 1);
                            v___x_3514_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once
                                ),
                                _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12,
                            );
                            v___x_3515_ = l_Lean_stringToMessageData(v_a_3513_);
                            v___x_3516_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3516_, 0, v___x_3514_);
                            leanh::lean_ctor_set(v___x_3516_, 1, v___x_3515_);
                            v___x_3517_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_3516_, v_a_3211_, v_a_3212_);
                            v___y_3509_ = v___x_3517_;
                            state = 41;
                            continue;
                        } else {
                            v_a_3518_ = leanh::lean_ctor_get(v_a_3512_, 0);
                            leanh::lean_inc(v_a_3518_);
                            leanh::lean_dec_ref_known(v_a_3512_, 1);
                            v_a_3487_ = v_a_3518_;
                            state = 38;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3218_);
                        v_a_3519_ = leanh::lean_ctor_get(v___x_3511_, 0);
                        v_isSharedCheck_3530_ =
                            (!leanh::lean_is_exclusive(v___x_3511_)) as u8;
                        if v_isSharedCheck_3530_ == 0 {
                            v___x_3521_ = v___x_3511_;
                            v_isShared_3522_ = v_isSharedCheck_3530_;
                            state = 42;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3519_);
                            leanh::lean_dec(v___x_3511_);
                            v___x_3521_ = leanh::lean_box(0);
                            v_isShared_3522_ = v_isSharedCheck_3530_;
                            state = 42;
                            continue;
                        }
                    }
                } else {
                    v___f_3531_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__13;
                    v___x_3532_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                    );
                    v___x_3533_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3221_,
                        v_options_3215_,
                        v___x_3532_,
                    );
                    if v___x_3533_ == 0 {
                        v___x_3628_ = l_Lean_trace_profiler;
                        v___x_3629_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_3215_, v___x_3628_);
                        if v___x_3629_ == 0 {
                            v___x_3630_ = l_IO_lazyPure___redArg(v___f_3224_);
                            if leanh::lean_obj_tag(v___x_3630_) == 0 {
                                v_a_3631_ = leanh::lean_ctor_get(v___x_3630_, 0);
                                leanh::lean_inc(v_a_3631_);
                                leanh::lean_dec_ref_known(v___x_3630_, 1);
                                if leanh::lean_obj_tag(v_a_3631_) == 0 {
                                    v_a_3632_ = leanh::lean_ctor_get(v_a_3631_, 0);
                                    leanh::lean_inc(v_a_3632_);
                                    leanh::lean_dec_ref_known(v_a_3631_, 1);
                                    v___x_3633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once), _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12);
                                    v___x_3634_ = l_Lean_stringToMessageData(v_a_3632_);
                                    v___x_3635_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3635_, 0, v___x_3633_);
                                    leanh::lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                                    v___x_3636_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_3635_, v_a_3211_, v_a_3212_);
                                    v___y_3509_ = v___x_3636_;
                                    state = 41;
                                    continue;
                                } else {
                                    v_a_3637_ = leanh::lean_ctor_get(v_a_3631_, 0);
                                    leanh::lean_inc(v_a_3637_);
                                    leanh::lean_dec_ref_known(v_a_3631_, 1);
                                    v_a_3487_ = v_a_3637_;
                                    state = 38;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_3218_);
                                v_a_3638_ = leanh::lean_ctor_get(v___x_3630_, 0);
                                v_isSharedCheck_3649_ =
                                    (!leanh::lean_is_exclusive(v___x_3630_)) as u8;
                                if v_isSharedCheck_3649_ == 0 {
                                    v___x_3640_ = v___x_3630_;
                                    v_isShared_3641_ = v_isSharedCheck_3649_;
                                    state = 55;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3638_);
                                    leanh::lean_dec(v___x_3630_);
                                    v___x_3640_ = leanh::lean_box(0);
                                    v_isShared_3641_ = v_isSharedCheck_3649_;
                                    state = 55;
                                    continue;
                                }
                            }
                        } else {
                            state = 50;
                            continue;
                        }
                    } else {
                        state = 50;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3232_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                );
                v___x_3233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_3230_,
                    v_options_3229_,
                    v___x_3232_,
                );
                if v___x_3233_ == 0 {
                    if v_isShared_3219_ == 0 {
                        leanh::lean_ctor_set(v___x_3218_, 0, v_proof_3227_);
                        v___x_3235_ = v___x_3218_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_proof_3227_);
                        v___x_3235_ = v_reuseFailAlloc_3236_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3218_);
                    v___x_3237_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7;
                    v___x_3238_ = lean_array_get_size(v_proof_3227_);
                    v___x_3239_ = l_Nat_reprFast(v___x_3238_);
                    v___x_3240_ = lean_string_append(v___x_3237_, v___x_3239_);
                    leanh::lean_dec_ref(v___x_3239_);
                    v___x_3241_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__8;
                    v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
                    v___x_3243_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3243_, 0, v___x_3242_);
                    v___x_3244_ = l_Lean_MessageData_ofFormat(v___x_3243_);
                    v___x_3245_ =
                        l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(
                            v___x_3225_,
                            v___x_3244_,
                            v___y_3228_,
                            v___y_3231_,
                        );
                    if leanh::lean_obj_tag(v___x_3245_) == 0 {
                        v_isSharedCheck_3252_ =
                            (!leanh::lean_is_exclusive(v___x_3245_)) as u8;
                        if v_isSharedCheck_3252_ == 0 {
                            v_unused_3253_ = leanh::lean_ctor_get(v___x_3245_, 0);
                            leanh::lean_dec(v_unused_3253_);
                            v___x_3247_ = v___x_3245_;
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3245_);
                            v___x_3247_ = leanh::lean_box(0);
                            v_isShared_3248_ = v_isSharedCheck_3252_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_proof_3227_);
                        v_a_3254_ = leanh::lean_ctor_get(v___x_3245_, 0);
                        v_isSharedCheck_3261_ =
                            (!leanh::lean_is_exclusive(v___x_3245_)) as u8;
                        if v_isSharedCheck_3261_ == 0 {
                            v___x_3256_ = v___x_3245_;
                            v_isShared_3257_ = v_isSharedCheck_3261_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3254_);
                            leanh::lean_dec(v___x_3245_);
                            v___x_3256_ = leanh::lean_box(0);
                            v_isShared_3257_ = v_isSharedCheck_3261_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3235_;
            }
            4 => {
                if v_isShared_3248_ == 0 {
                    leanh::lean_ctor_set(v___x_3247_, 0, v_proof_3227_);
                    v___x_3250_ = v___x_3247_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_proof_3227_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3250_;
            }
            6 => {
                if v_isShared_3257_ == 0 {
                    v___x_3259_ = v___x_3256_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3260_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
                    v___x_3259_ = v_reuseFailAlloc_3260_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3259_;
            }
            8 => {
                v_options_3266_ = leanh::lean_ctor_get(v___y_3264_, 2);
                v_hasTrace_3267_ = leanh::lean_ctor_get_uint8(
                    v_options_3266_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3267_ == 0 {
                    leanh::lean_del_object(v___x_3218_);
                    v___x_3268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3268_, 0, v_proof_3263_);
                    return v___x_3268_;
                } else {
                    v_inheritedTraceOptions_3269_ = leanh::lean_ctor_get(v___y_3264_, 13);
                    v_proof_3227_ = v_proof_3263_;
                    v___y_3228_ = v___y_3264_;
                    v_options_3229_ = v_options_3266_;
                    v_inheritedTraceOptions_3230_ = v_inheritedTraceOptions_3269_;
                    v___y_3231_ = v___y_3265_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                if leanh::lean_obj_tag(v___y_3273_) == 0 {
                    v_a_3274_ = leanh::lean_ctor_get(v___y_3273_, 0);
                    leanh::lean_inc(v_a_3274_);
                    leanh::lean_dec_ref_known(v___y_3273_, 1);
                    v_proof_3263_ = v_a_3274_;
                    v___y_3264_ = v___y_3272_;
                    v___y_3265_ = v___y_3271_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3218_);
                    return v___y_3273_;
                }
            }
            10 => {
                v___x_3285_ = lean_io_get_num_heartbeats();
                v___x_3286_ = lean_float_of_nat(v___y_3283_);
                v___x_3287_ = lean_float_of_nat(v___x_3285_);
                v___x_3288_ = leanh::lean_box_float(v___x_3286_);
                v___x_3289_ = leanh::lean_box_float(v___x_3287_);
                v___x_3290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3290_, 0, v___x_3288_);
                leanh::lean_ctor_set(v___x_3290_, 1, v___x_3289_);
                v___x_3291_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3291_, 0, v_a_3284_);
                leanh::lean_ctor_set(v___x_3291_, 1, v___x_3290_);
                v___x_3292_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_3225_, v___x_3275_, v___x_3276_, v___y_3280_, v___y_3279_, v___y_3278_, v___f_3223_, v___x_3291_, v___y_3282_, v___y_3281_);
                v___y_3271_ = v___y_3281_;
                v___y_3272_ = v___y_3282_;
                v___y_3273_ = v___x_3292_;
                state = 9;
                continue;
            }
            11 => {
                v___x_3301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3301_, 0, v_a_3300_);
                v___y_3278_ = v___y_3294_;
                v___y_3279_ = v___y_3295_;
                v___y_3280_ = v___y_3296_;
                v___y_3281_ = v___y_3297_;
                v___y_3282_ = v___y_3299_;
                v___y_3283_ = v___y_3298_;
                v_a_3284_ = v___x_3301_;
                state = 10;
                continue;
            }
            12 => {
                v___x_3310_ = lean_io_mono_nanos_now();
                v___x_3311_ = lean_float_of_nat(v___y_3307_);
                v___x_3312_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9,
                );
                v___x_3313_ = lean_float_div(v___x_3311_, v___x_3312_);
                v___x_3314_ = lean_float_of_nat(v___x_3310_);
                v___x_3315_ = lean_float_div(v___x_3314_, v___x_3312_);
                v___x_3316_ = leanh::lean_box_float(v___x_3313_);
                v___x_3317_ = leanh::lean_box_float(v___x_3315_);
                v___x_3318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3318_, 0, v___x_3316_);
                leanh::lean_ctor_set(v___x_3318_, 1, v___x_3317_);
                v___x_3319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3319_, 0, v_a_3309_);
                leanh::lean_ctor_set(v___x_3319_, 1, v___x_3318_);
                v___x_3320_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_3225_, v___x_3275_, v___x_3276_, v___y_3305_, v___y_3304_, v___y_3303_, v___f_3223_, v___x_3319_, v___y_3308_, v___y_3306_);
                v___y_3271_ = v___y_3306_;
                v___y_3272_ = v___y_3308_;
                v___y_3273_ = v___x_3320_;
                state = 9;
                continue;
            }
            13 => {
                v___x_3329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3329_, 0, v_a_3328_);
                v___y_3303_ = v___y_3322_;
                v___y_3304_ = v___y_3323_;
                v___y_3305_ = v___y_3324_;
                v___y_3306_ = v___y_3325_;
                v___y_3307_ = v___y_3326_;
                v___y_3308_ = v___y_3327_;
                v_a_3309_ = v___x_3329_;
                state = 12;
                continue;
            }
            14 => {
                v___x_3337_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_3335_);
                v_a_3338_ = leanh::lean_ctor_get(v___x_3337_, 0);
                leanh::lean_inc(v_a_3338_);
                leanh::lean_dec_ref(v___x_3337_);
                v___x_3339_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3340_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v___y_3334_,
                        v___x_3339_,
                    );
                if v___x_3340_ == 0 {
                    v___x_3341_ = lean_io_mono_nanos_now();
                    v___x_3342_ = l_IO_lazyPure___redArg(v___y_3332_);
                    if leanh::lean_obj_tag(v___x_3342_) == 0 {
                        v_a_3343_ = leanh::lean_ctor_get(v___x_3342_, 0);
                        leanh::lean_inc(v_a_3343_);
                        leanh::lean_dec_ref_known(v___x_3342_, 1);
                        v___x_3344_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_3343_);
                        if leanh::lean_obj_tag(v___x_3344_) == 0 {
                            v_a_3345_ = leanh::lean_ctor_get(v___x_3344_, 0);
                            v_isSharedCheck_3352_ =
                                (!leanh::lean_is_exclusive(v___x_3344_)) as u8;
                            if v_isSharedCheck_3352_ == 0 {
                                v___x_3347_ = v___x_3344_;
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3345_);
                                leanh::lean_dec(v___x_3344_);
                                v___x_3347_ = leanh::lean_box(0);
                                v_isShared_3348_ = v_isSharedCheck_3352_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_3353_ = leanh::lean_ctor_get(v___x_3344_, 0);
                            v_isSharedCheck_3363_ =
                                (!leanh::lean_is_exclusive(v___x_3344_)) as u8;
                            if v_isSharedCheck_3363_ == 0 {
                                v___x_3355_ = v___x_3344_;
                                v_isShared_3356_ = v_isSharedCheck_3363_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3353_);
                                leanh::lean_dec(v___x_3344_);
                                v___x_3355_ = leanh::lean_box(0);
                                v_isShared_3356_ = v_isSharedCheck_3363_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        v_a_3364_ = leanh::lean_ctor_get(v___x_3342_, 0);
                        v_isSharedCheck_3374_ =
                            (!leanh::lean_is_exclusive(v___x_3342_)) as u8;
                        if v_isSharedCheck_3374_ == 0 {
                            v___x_3366_ = v___x_3342_;
                            v_isShared_3367_ = v_isSharedCheck_3374_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3364_);
                            leanh::lean_dec(v___x_3342_);
                            v___x_3366_ = leanh::lean_box(0);
                            v_isShared_3367_ = v_isSharedCheck_3374_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v___x_3375_ = lean_io_get_num_heartbeats();
                    v___x_3376_ = l_IO_lazyPure___redArg(v___y_3332_);
                    if leanh::lean_obj_tag(v___x_3376_) == 0 {
                        v_a_3377_ = leanh::lean_ctor_get(v___x_3376_, 0);
                        leanh::lean_inc(v_a_3377_);
                        leanh::lean_dec_ref_known(v___x_3376_, 1);
                        v___x_3378_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_3377_);
                        if leanh::lean_obj_tag(v___x_3378_) == 0 {
                            v_a_3379_ = leanh::lean_ctor_get(v___x_3378_, 0);
                            v_isSharedCheck_3386_ =
                                (!leanh::lean_is_exclusive(v___x_3378_)) as u8;
                            if v_isSharedCheck_3386_ == 0 {
                                v___x_3381_ = v___x_3378_;
                                v_isShared_3382_ = v_isSharedCheck_3386_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3379_);
                                leanh::lean_dec(v___x_3378_);
                                v___x_3381_ = leanh::lean_box(0);
                                v_isShared_3382_ = v_isSharedCheck_3386_;
                                state = 21;
                                continue;
                            }
                        } else {
                            v_a_3387_ = leanh::lean_ctor_get(v___x_3378_, 0);
                            v_isSharedCheck_3397_ =
                                (!leanh::lean_is_exclusive(v___x_3378_)) as u8;
                            if v_isSharedCheck_3397_ == 0 {
                                v___x_3389_ = v___x_3378_;
                                v_isShared_3390_ = v_isSharedCheck_3397_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3387_);
                                leanh::lean_dec(v___x_3378_);
                                v___x_3389_ = leanh::lean_box(0);
                                v_isShared_3390_ = v_isSharedCheck_3397_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        v_a_3398_ = leanh::lean_ctor_get(v___x_3376_, 0);
                        v_isSharedCheck_3408_ =
                            (!leanh::lean_is_exclusive(v___x_3376_)) as u8;
                        if v_isSharedCheck_3408_ == 0 {
                            v___x_3400_ = v___x_3376_;
                            v_isShared_3401_ = v_isSharedCheck_3408_;
                            state = 25;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3398_);
                            leanh::lean_dec(v___x_3376_);
                            v___x_3400_ = leanh::lean_box(0);
                            v_isShared_3401_ = v_isSharedCheck_3408_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_3348_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3347_, 1);
                    v___x_3350_ = v___x_3347_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
                    v___x_3350_ = v_reuseFailAlloc_3351_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_3303_ = v_a_3338_;
                v___y_3304_ = v___y_3333_;
                v___y_3305_ = v___y_3334_;
                v___y_3306_ = v___y_3335_;
                v___y_3307_ = v___x_3341_;
                v___y_3308_ = v___y_3336_;
                v_a_3309_ = v___x_3350_;
                state = 12;
                continue;
            }
            17 => {
                v___x_3357_ = lean_io_error_to_string(v_a_3353_);
                if v_isShared_3356_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3355_, 3);
                    leanh::lean_ctor_set(v___x_3355_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3355_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3357_);
                    v___x_3359_ = v_reuseFailAlloc_3362_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3360_ = l_Lean_MessageData_ofFormat(v___x_3359_);
                leanh::lean_inc(v___y_3331_);
                v___x_3361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3361_, 0, v___y_3331_);
                leanh::lean_ctor_set(v___x_3361_, 1, v___x_3360_);
                v___y_3322_ = v_a_3338_;
                v___y_3323_ = v___y_3333_;
                v___y_3324_ = v___y_3334_;
                v___y_3325_ = v___y_3335_;
                v___y_3326_ = v___x_3341_;
                v___y_3327_ = v___y_3336_;
                v_a_3328_ = v___x_3361_;
                state = 13;
                continue;
            }
            19 => {
                v___x_3368_ = lean_io_error_to_string(v_a_3364_);
                if v_isShared_3367_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3366_, 3);
                    leanh::lean_ctor_set(v___x_3366_, 0, v___x_3368_);
                    v___x_3370_ = v___x_3366_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3368_);
                    v___x_3370_ = v_reuseFailAlloc_3373_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3371_ = l_Lean_MessageData_ofFormat(v___x_3370_);
                leanh::lean_inc(v___y_3331_);
                v___x_3372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3372_, 0, v___y_3331_);
                leanh::lean_ctor_set(v___x_3372_, 1, v___x_3371_);
                v___y_3322_ = v_a_3338_;
                v___y_3323_ = v___y_3333_;
                v___y_3324_ = v___y_3334_;
                v___y_3325_ = v___y_3335_;
                v___y_3326_ = v___x_3341_;
                v___y_3327_ = v___y_3336_;
                v_a_3328_ = v___x_3372_;
                state = 13;
                continue;
            }
            21 => {
                if v_isShared_3382_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3381_, 1);
                    v___x_3384_ = v___x_3381_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_3278_ = v_a_3338_;
                v___y_3279_ = v___y_3333_;
                v___y_3280_ = v___y_3334_;
                v___y_3281_ = v___y_3335_;
                v___y_3282_ = v___y_3336_;
                v___y_3283_ = v___x_3375_;
                v_a_3284_ = v___x_3384_;
                state = 10;
                continue;
            }
            23 => {
                v___x_3391_ = lean_io_error_to_string(v_a_3387_);
                if v_isShared_3390_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3389_, 3);
                    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3391_);
                    v___x_3393_ = v___x_3389_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3396_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3391_);
                    v___x_3393_ = v_reuseFailAlloc_3396_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3394_ = l_Lean_MessageData_ofFormat(v___x_3393_);
                leanh::lean_inc(v___y_3331_);
                v___x_3395_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3395_, 0, v___y_3331_);
                leanh::lean_ctor_set(v___x_3395_, 1, v___x_3394_);
                v___y_3294_ = v_a_3338_;
                v___y_3295_ = v___y_3333_;
                v___y_3296_ = v___y_3334_;
                v___y_3297_ = v___y_3335_;
                v___y_3298_ = v___x_3375_;
                v___y_3299_ = v___y_3336_;
                v_a_3300_ = v___x_3395_;
                state = 11;
                continue;
            }
            25 => {
                v___x_3402_ = lean_io_error_to_string(v_a_3398_);
                if v_isShared_3401_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3400_, 3);
                    leanh::lean_ctor_set(v___x_3400_, 0, v___x_3402_);
                    v___x_3404_ = v___x_3400_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3407_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3402_);
                    v___x_3404_ = v_reuseFailAlloc_3407_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3405_ = l_Lean_MessageData_ofFormat(v___x_3404_);
                leanh::lean_inc(v___y_3331_);
                v___x_3406_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3406_, 0, v___y_3331_);
                leanh::lean_ctor_set(v___x_3406_, 1, v___x_3405_);
                v___y_3294_ = v_a_3338_;
                v___y_3295_ = v___y_3333_;
                v___y_3296_ = v___y_3334_;
                v___y_3297_ = v___y_3335_;
                v___y_3298_ = v___x_3375_;
                v___y_3299_ = v___y_3336_;
                v_a_3300_ = v___x_3406_;
                state = 11;
                continue;
            }
            27 => {
                if v_trimProofs_3210_ == 0 {
                    leanh::lean_dec_ref(v___y_3410_);
                    v_proof_3263_ = v___y_3411_;
                    v___y_3264_ = v___y_3412_;
                    v___y_3265_ = v___y_3413_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___y_3411_);
                    v_options_3414_ = leanh::lean_ctor_get(v___y_3412_, 2);
                    v_hasTrace_3415_ = leanh::lean_ctor_get_uint8(
                        v_options_3414_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3415_ == 0 {
                        leanh::lean_del_object(v___x_3218_);
                        v_ref_3416_ = leanh::lean_ctor_get(v___y_3412_, 5);
                        v___x_3417_ = l_IO_lazyPure___redArg(v___y_3410_);
                        if leanh::lean_obj_tag(v___x_3417_) == 0 {
                            v_a_3418_ = leanh::lean_ctor_get(v___x_3417_, 0);
                            leanh::lean_inc(v_a_3418_);
                            leanh::lean_dec_ref_known(v___x_3417_, 1);
                            v___x_3419_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_3418_);
                            if leanh::lean_obj_tag(v___x_3419_) == 0 {
                                v_a_3420_ = leanh::lean_ctor_get(v___x_3419_, 0);
                                v_isSharedCheck_3427_ =
                                    (!leanh::lean_is_exclusive(v___x_3419_)) as u8;
                                if v_isSharedCheck_3427_ == 0 {
                                    v___x_3422_ = v___x_3419_;
                                    v_isShared_3423_ = v_isSharedCheck_3427_;
                                    state = 28;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3420_);
                                    leanh::lean_dec(v___x_3419_);
                                    v___x_3422_ = leanh::lean_box(0);
                                    v_isShared_3423_ = v_isSharedCheck_3427_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                v_a_3428_ = leanh::lean_ctor_get(v___x_3419_, 0);
                                v_isSharedCheck_3439_ =
                                    (!leanh::lean_is_exclusive(v___x_3419_)) as u8;
                                if v_isSharedCheck_3439_ == 0 {
                                    v___x_3430_ = v___x_3419_;
                                    v_isShared_3431_ = v_isSharedCheck_3439_;
                                    state = 30;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3428_);
                                    leanh::lean_dec(v___x_3419_);
                                    v___x_3430_ = leanh::lean_box(0);
                                    v_isShared_3431_ = v_isSharedCheck_3439_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3440_ = leanh::lean_ctor_get(v___x_3417_, 0);
                            v_isSharedCheck_3451_ =
                                (!leanh::lean_is_exclusive(v___x_3417_)) as u8;
                            if v_isSharedCheck_3451_ == 0 {
                                v___x_3442_ = v___x_3417_;
                                v_isShared_3443_ = v_isSharedCheck_3451_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3440_);
                                leanh::lean_dec(v___x_3417_);
                                v___x_3442_ = leanh::lean_box(0);
                                v_isShared_3443_ = v_isSharedCheck_3451_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        v_ref_3452_ = leanh::lean_ctor_get(v___y_3412_, 5);
                        v_inheritedTraceOptions_3453_ =
                            leanh::lean_ctor_get(v___y_3412_, 13);
                        v___x_3454_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                        );
                        v___x_3455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3453_,
                            v_options_3414_,
                            v___x_3454_,
                        );
                        if v___x_3455_ == 0 {
                            v___x_3456_ = l_Lean_trace_profiler;
                            v___x_3457_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_3414_, v___x_3456_);
                            if v___x_3457_ == 0 {
                                v___x_3458_ = l_IO_lazyPure___redArg(v___y_3410_);
                                if leanh::lean_obj_tag(v___x_3458_) == 0 {
                                    v_a_3459_ = leanh::lean_ctor_get(v___x_3458_, 0);
                                    leanh::lean_inc(v_a_3459_);
                                    leanh::lean_dec_ref_known(v___x_3458_, 1);
                                    v___x_3460_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__4___redArg(v_a_3459_);
                                    if leanh::lean_obj_tag(v___x_3460_) == 0 {
                                        v_a_3461_ = leanh::lean_ctor_get(v___x_3460_, 0);
                                        leanh::lean_inc(v_a_3461_);
                                        leanh::lean_dec_ref_known(v___x_3460_, 1);
                                        v_proof_3227_ = v_a_3461_;
                                        v___y_3228_ = v___y_3412_;
                                        v_options_3229_ = v_options_3414_;
                                        v_inheritedTraceOptions_3230_ =
                                            v_inheritedTraceOptions_3453_;
                                        v___y_3231_ = v___y_3413_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_del_object(v___x_3218_);
                                        v_a_3462_ = leanh::lean_ctor_get(v___x_3460_, 0);
                                        v_isSharedCheck_3473_ =
                                            (!leanh::lean_is_exclusive(v___x_3460_)) as u8;
                                        if v_isSharedCheck_3473_ == 0 {
                                            v___x_3464_ = v___x_3460_;
                                            v_isShared_3465_ = v_isSharedCheck_3473_;
                                            state = 34;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3462_);
                                            leanh::lean_dec(v___x_3460_);
                                            v___x_3464_ = leanh::lean_box(0);
                                            v_isShared_3465_ = v_isSharedCheck_3473_;
                                            state = 34;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_3218_);
                                    v_a_3474_ = leanh::lean_ctor_get(v___x_3458_, 0);
                                    v_isSharedCheck_3485_ =
                                        (!leanh::lean_is_exclusive(v___x_3458_)) as u8;
                                    if v_isSharedCheck_3485_ == 0 {
                                        v___x_3476_ = v___x_3458_;
                                        v_isShared_3477_ = v_isSharedCheck_3485_;
                                        state = 36;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3474_);
                                        leanh::lean_dec(v___x_3458_);
                                        v___x_3476_ = leanh::lean_box(0);
                                        v_isShared_3477_ = v_isSharedCheck_3485_;
                                        state = 36;
                                        continue;
                                    }
                                }
                            } else {
                                v___y_3331_ = v_ref_3452_;
                                v___y_3332_ = v___y_3410_;
                                v___y_3333_ = v___x_3455_;
                                v___y_3334_ = v_options_3414_;
                                v___y_3335_ = v___y_3413_;
                                v___y_3336_ = v___y_3412_;
                                state = 14;
                                continue;
                            }
                        } else {
                            v___y_3331_ = v_ref_3452_;
                            v___y_3332_ = v___y_3410_;
                            v___y_3333_ = v___x_3455_;
                            v___y_3334_ = v_options_3414_;
                            v___y_3335_ = v___y_3413_;
                            v___y_3336_ = v___y_3412_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            28 => {
                if v_isShared_3423_ == 0 {
                    v___x_3425_ = v___x_3422_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3426_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
                    v___x_3425_ = v_reuseFailAlloc_3426_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3425_;
            }
            30 => {
                v___x_3432_ = lean_io_error_to_string(v_a_3428_);
                v___x_3433_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                v___x_3434_ = l_Lean_MessageData_ofFormat(v___x_3433_);
                leanh::lean_inc(v_ref_3416_);
                v___x_3435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3435_, 0, v_ref_3416_);
                leanh::lean_ctor_set(v___x_3435_, 1, v___x_3434_);
                if v_isShared_3431_ == 0 {
                    leanh::lean_ctor_set(v___x_3430_, 0, v___x_3435_);
                    v___x_3437_ = v___x_3430_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3437_;
            }
            32 => {
                v___x_3444_ = lean_io_error_to_string(v_a_3440_);
                v___x_3445_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3445_, 0, v___x_3444_);
                v___x_3446_ = l_Lean_MessageData_ofFormat(v___x_3445_);
                leanh::lean_inc(v_ref_3416_);
                v___x_3447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3447_, 0, v_ref_3416_);
                leanh::lean_ctor_set(v___x_3447_, 1, v___x_3446_);
                if v_isShared_3443_ == 0 {
                    leanh::lean_ctor_set(v___x_3442_, 0, v___x_3447_);
                    v___x_3449_ = v___x_3442_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
                    v___x_3449_ = v_reuseFailAlloc_3450_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3449_;
            }
            34 => {
                v___x_3466_ = lean_io_error_to_string(v_a_3462_);
                v___x_3467_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3467_, 0, v___x_3466_);
                v___x_3468_ = l_Lean_MessageData_ofFormat(v___x_3467_);
                leanh::lean_inc(v_ref_3452_);
                v___x_3469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3469_, 0, v_ref_3452_);
                leanh::lean_ctor_set(v___x_3469_, 1, v___x_3468_);
                if v_isShared_3465_ == 0 {
                    leanh::lean_ctor_set(v___x_3464_, 0, v___x_3469_);
                    v___x_3471_ = v___x_3464_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
                    v___x_3471_ = v_reuseFailAlloc_3472_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3471_;
            }
            36 => {
                v___x_3478_ = lean_io_error_to_string(v_a_3474_);
                v___x_3479_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3479_, 0, v___x_3478_);
                v___x_3480_ = l_Lean_MessageData_ofFormat(v___x_3479_);
                leanh::lean_inc(v_ref_3452_);
                v___x_3481_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3481_, 0, v_ref_3452_);
                leanh::lean_ctor_set(v___x_3481_, 1, v___x_3480_);
                if v_isShared_3477_ == 0 {
                    leanh::lean_ctor_set(v___x_3476_, 0, v___x_3481_);
                    v___x_3483_ = v___x_3476_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3483_;
            }
            38 => {
                leanh::lean_inc_ref(v_a_3487_);
                v___f_3488_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___lam__2___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3488_, 0, v_a_3487_);
                if v_hasTrace_3222_ == 0 {
                    v___y_3410_ = v___f_3488_;
                    v___y_3411_ = v_a_3487_;
                    v___y_3412_ = v_a_3211_;
                    v___y_3413_ = v_a_3212_;
                    state = 27;
                    continue;
                } else {
                    v___x_3489_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                    );
                    v___x_3490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3221_,
                        v_options_3215_,
                        v___x_3489_,
                    );
                    if v___x_3490_ == 0 {
                        v___y_3410_ = v___f_3488_;
                        v___y_3411_ = v_a_3487_;
                        v___y_3412_ = v_a_3211_;
                        v___y_3413_ = v_a_3212_;
                        state = 27;
                        continue;
                    } else {
                        v___x_3491_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__7;
                        v___x_3492_ = lean_array_get_size(v_a_3487_);
                        v___x_3493_ = l_Nat_reprFast(v___x_3492_);
                        v___x_3494_ = lean_string_append(v___x_3491_, v___x_3493_);
                        leanh::lean_dec_ref(v___x_3493_);
                        v___x_3495_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__10;
                        v___x_3496_ = lean_string_append(v___x_3494_, v___x_3495_);
                        v___x_3497_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3497_, 0, v___x_3496_);
                        v___x_3498_ = l_Lean_MessageData_ofFormat(v___x_3497_);
                        v___x_3499_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0(v___x_3225_, v___x_3498_, v_a_3211_, v_a_3212_);
                        if leanh::lean_obj_tag(v___x_3499_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3499_, 1);
                            v___y_3410_ = v___f_3488_;
                            v___y_3411_ = v_a_3487_;
                            v___y_3412_ = v_a_3211_;
                            v___y_3413_ = v_a_3212_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___f_3488_);
                            leanh::lean_dec_ref(v_a_3487_);
                            leanh::lean_del_object(v___x_3218_);
                            v_a_3500_ = leanh::lean_ctor_get(v___x_3499_, 0);
                            v_isSharedCheck_3507_ =
                                (!leanh::lean_is_exclusive(v___x_3499_)) as u8;
                            if v_isSharedCheck_3507_ == 0 {
                                v___x_3502_ = v___x_3499_;
                                v_isShared_3503_ = v_isSharedCheck_3507_;
                                state = 39;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3500_);
                                leanh::lean_dec(v___x_3499_);
                                v___x_3502_ = leanh::lean_box(0);
                                v_isShared_3503_ = v_isSharedCheck_3507_;
                                state = 39;
                                continue;
                            }
                        }
                    }
                }
            }
            39 => {
                if v_isShared_3503_ == 0 {
                    v___x_3505_ = v___x_3502_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
                    v___x_3505_ = v_reuseFailAlloc_3506_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3505_;
            }
            41 => {
                if leanh::lean_obj_tag(v___y_3509_) == 0 {
                    v_a_3510_ = leanh::lean_ctor_get(v___y_3509_, 0);
                    leanh::lean_inc(v_a_3510_);
                    leanh::lean_dec_ref_known(v___y_3509_, 1);
                    v_a_3487_ = v_a_3510_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3218_);
                    return v___y_3509_;
                }
            }
            42 => {
                v___x_3523_ = lean_io_error_to_string(v_a_3519_);
                v___x_3524_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3524_, 0, v___x_3523_);
                v___x_3525_ = l_Lean_MessageData_ofFormat(v___x_3524_);
                leanh::lean_inc(v_ref_3220_);
                v___x_3526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3526_, 0, v_ref_3220_);
                leanh::lean_ctor_set(v___x_3526_, 1, v___x_3525_);
                if v_isShared_3522_ == 0 {
                    leanh::lean_ctor_set(v___x_3521_, 0, v___x_3526_);
                    v___x_3528_ = v___x_3521_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
                    v___x_3528_ = v_reuseFailAlloc_3529_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3528_;
            }
            44 => {
                v___x_3538_ = lean_io_mono_nanos_now();
                v___x_3539_ = lean_float_of_nat(v___y_3535_);
                v___x_3540_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9,
                );
                v___x_3541_ = lean_float_div(v___x_3539_, v___x_3540_);
                v___x_3542_ = lean_float_of_nat(v___x_3538_);
                v___x_3543_ = lean_float_div(v___x_3542_, v___x_3540_);
                v___x_3544_ = leanh::lean_box_float(v___x_3541_);
                v___x_3545_ = leanh::lean_box_float(v___x_3543_);
                v___x_3546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3546_, 0, v___x_3544_);
                leanh::lean_ctor_set(v___x_3546_, 1, v___x_3545_);
                v___x_3547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3547_, 0, v_a_3537_);
                leanh::lean_ctor_set(v___x_3547_, 1, v___x_3546_);
                v___x_3548_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_3225_, v___x_3275_, v___x_3276_, v_options_3215_, v___x_3533_, v___y_3536_, v___f_3531_, v___x_3547_, v_a_3211_, v_a_3212_);
                v___y_3509_ = v___x_3548_;
                state = 41;
                continue;
            }
            45 => {
                v___x_3553_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3553_, 0, v_a_3552_);
                v___y_3535_ = v___y_3550_;
                v___y_3536_ = v___y_3551_;
                v_a_3537_ = v___x_3553_;
                state = 44;
                continue;
            }
            46 => {
                v___x_3558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3558_, 0, v_a_3557_);
                v___y_3535_ = v___y_3555_;
                v___y_3536_ = v___y_3556_;
                v_a_3537_ = v___x_3558_;
                state = 44;
                continue;
            }
            47 => {
                v___x_3563_ = lean_io_get_num_heartbeats();
                v___x_3564_ = lean_float_of_nat(v___y_3560_);
                v___x_3565_ = lean_float_of_nat(v___x_3563_);
                v___x_3566_ = leanh::lean_box_float(v___x_3564_);
                v___x_3567_ = leanh::lean_box_float(v___x_3565_);
                v___x_3568_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3568_, 0, v___x_3566_);
                leanh::lean_ctor_set(v___x_3568_, 1, v___x_3567_);
                v___x_3569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3569_, 0, v_a_3562_);
                leanh::lean_ctor_set(v___x_3569_, 1, v___x_3568_);
                v___x_3570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3(v___x_3225_, v___x_3275_, v___x_3276_, v_options_3215_, v___x_3533_, v___y_3561_, v___f_3531_, v___x_3569_, v_a_3211_, v_a_3212_);
                v___y_3509_ = v___x_3570_;
                state = 41;
                continue;
            }
            48 => {
                v___x_3575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3575_, 0, v_a_3574_);
                v___y_3560_ = v___y_3572_;
                v___y_3561_ = v___y_3573_;
                v_a_3562_ = v___x_3575_;
                state = 47;
                continue;
            }
            49 => {
                v___x_3580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3580_, 0, v_a_3579_);
                v___y_3560_ = v___y_3577_;
                v___y_3561_ = v___y_3578_;
                v_a_3562_ = v___x_3580_;
                state = 47;
                continue;
            }
            50 => {
                v___x_3582_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v_a_3212_);
                v_a_3583_ = leanh::lean_ctor_get(v___x_3582_, 0);
                leanh::lean_inc(v_a_3583_);
                leanh::lean_dec_ref(v___x_3582_);
                v___x_3584_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_3585_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_options_3215_,
                        v___x_3584_,
                    );
                if v___x_3585_ == 0 {
                    v___x_3586_ = lean_io_mono_nanos_now();
                    v___x_3587_ = l_IO_lazyPure___redArg(v___f_3224_);
                    if leanh::lean_obj_tag(v___x_3587_) == 0 {
                        v_a_3588_ = leanh::lean_ctor_get(v___x_3587_, 0);
                        leanh::lean_inc(v_a_3588_);
                        leanh::lean_dec_ref_known(v___x_3587_, 1);
                        if leanh::lean_obj_tag(v_a_3588_) == 0 {
                            v_a_3589_ = leanh::lean_ctor_get(v_a_3588_, 0);
                            leanh::lean_inc(v_a_3589_);
                            leanh::lean_dec_ref_known(v_a_3588_, 1);
                            v___x_3590_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once
                                ),
                                _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12,
                            );
                            v___x_3591_ = l_Lean_stringToMessageData(v_a_3589_);
                            v___x_3592_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3592_, 0, v___x_3590_);
                            leanh::lean_ctor_set(v___x_3592_, 1, v___x_3591_);
                            v___x_3593_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_3592_, v_a_3211_, v_a_3212_);
                            v_a_3594_ = leanh::lean_ctor_get(v___x_3593_, 0);
                            leanh::lean_inc(v_a_3594_);
                            leanh::lean_dec_ref(v___x_3593_);
                            v___y_3550_ = v___x_3586_;
                            v___y_3551_ = v_a_3583_;
                            v_a_3552_ = v_a_3594_;
                            state = 45;
                            continue;
                        } else {
                            v_a_3595_ = leanh::lean_ctor_get(v_a_3588_, 0);
                            leanh::lean_inc(v_a_3595_);
                            leanh::lean_dec_ref_known(v_a_3588_, 1);
                            v___y_3555_ = v___x_3586_;
                            v___y_3556_ = v_a_3583_;
                            v_a_3557_ = v_a_3595_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v_a_3596_ = leanh::lean_ctor_get(v___x_3587_, 0);
                        v_isSharedCheck_3606_ =
                            (!leanh::lean_is_exclusive(v___x_3587_)) as u8;
                        if v_isSharedCheck_3606_ == 0 {
                            v___x_3598_ = v___x_3587_;
                            v_isShared_3599_ = v_isSharedCheck_3606_;
                            state = 51;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3596_);
                            leanh::lean_dec(v___x_3587_);
                            v___x_3598_ = leanh::lean_box(0);
                            v_isShared_3599_ = v_isSharedCheck_3606_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    v___x_3607_ = lean_io_get_num_heartbeats();
                    v___x_3608_ = l_IO_lazyPure___redArg(v___f_3224_);
                    if leanh::lean_obj_tag(v___x_3608_) == 0 {
                        v_a_3609_ = leanh::lean_ctor_get(v___x_3608_, 0);
                        leanh::lean_inc(v_a_3609_);
                        leanh::lean_dec_ref_known(v___x_3608_, 1);
                        if leanh::lean_obj_tag(v_a_3609_) == 0 {
                            v_a_3610_ = leanh::lean_ctor_get(v_a_3609_, 0);
                            leanh::lean_inc(v_a_3610_);
                            leanh::lean_dec_ref_known(v_a_3609_, 1);
                            v___x_3611_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12_once
                                ),
                                _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__12,
                            );
                            v___x_3612_ = l_Lean_stringToMessageData(v_a_3610_);
                            v___x_3613_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                            leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                            v___x_3614_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(v___x_3613_, v_a_3211_, v_a_3212_);
                            v_a_3615_ = leanh::lean_ctor_get(v___x_3614_, 0);
                            leanh::lean_inc(v_a_3615_);
                            leanh::lean_dec_ref(v___x_3614_);
                            v___y_3572_ = v___x_3607_;
                            v___y_3573_ = v_a_3583_;
                            v_a_3574_ = v_a_3615_;
                            state = 48;
                            continue;
                        } else {
                            v_a_3616_ = leanh::lean_ctor_get(v_a_3609_, 0);
                            leanh::lean_inc(v_a_3616_);
                            leanh::lean_dec_ref_known(v_a_3609_, 1);
                            v___y_3577_ = v___x_3607_;
                            v___y_3578_ = v_a_3583_;
                            v_a_3579_ = v_a_3616_;
                            state = 49;
                            continue;
                        }
                    } else {
                        v_a_3617_ = leanh::lean_ctor_get(v___x_3608_, 0);
                        v_isSharedCheck_3627_ =
                            (!leanh::lean_is_exclusive(v___x_3608_)) as u8;
                        if v_isSharedCheck_3627_ == 0 {
                            v___x_3619_ = v___x_3608_;
                            v_isShared_3620_ = v_isSharedCheck_3627_;
                            state = 53;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3617_);
                            leanh::lean_dec(v___x_3608_);
                            v___x_3619_ = leanh::lean_box(0);
                            v_isShared_3620_ = v_isSharedCheck_3627_;
                            state = 53;
                            continue;
                        }
                    }
                }
            }
            51 => {
                v___x_3600_ = lean_io_error_to_string(v_a_3596_);
                if v_isShared_3599_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3598_, 3);
                    leanh::lean_ctor_set(v___x_3598_, 0, v___x_3600_);
                    v___x_3602_ = v___x_3598_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_3605_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3600_);
                    v___x_3602_ = v_reuseFailAlloc_3605_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                v___x_3603_ = l_Lean_MessageData_ofFormat(v___x_3602_);
                leanh::lean_inc(v_ref_3220_);
                v___x_3604_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3604_, 0, v_ref_3220_);
                leanh::lean_ctor_set(v___x_3604_, 1, v___x_3603_);
                v___y_3550_ = v___x_3586_;
                v___y_3551_ = v_a_3583_;
                v_a_3552_ = v___x_3604_;
                state = 45;
                continue;
            }
            53 => {
                v___x_3621_ = lean_io_error_to_string(v_a_3617_);
                if v_isShared_3620_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3619_, 3);
                    leanh::lean_ctor_set(v___x_3619_, 0, v___x_3621_);
                    v___x_3623_ = v___x_3619_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3621_);
                    v___x_3623_ = v_reuseFailAlloc_3626_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_3624_ = l_Lean_MessageData_ofFormat(v___x_3623_);
                leanh::lean_inc(v_ref_3220_);
                v___x_3625_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3625_, 0, v_ref_3220_);
                leanh::lean_ctor_set(v___x_3625_, 1, v___x_3624_);
                v___y_3572_ = v___x_3607_;
                v___y_3573_ = v_a_3583_;
                v_a_3574_ = v___x_3625_;
                state = 48;
                continue;
            }
            55 => {
                v___x_3642_ = lean_io_error_to_string(v_a_3638_);
                v___x_3643_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                v___x_3644_ = l_Lean_MessageData_ofFormat(v___x_3643_);
                leanh::lean_inc(v_ref_3220_);
                v___x_3645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3645_, 0, v_ref_3220_);
                leanh::lean_ctor_set(v___x_3645_, 1, v___x_3644_);
                if v_isShared_3641_ == 0 {
                    leanh::lean_ctor_set(v___x_3640_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3640_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
                    v___x_3647_ = v_reuseFailAlloc_3648_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_3647_;
            }
            57 => {
                v_ref_3655_ = leanh::lean_ctor_get(v_a_3211_, 5);
                v___x_3656_ = lean_io_error_to_string(v_a_3651_);
                v___x_3657_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3657_, 0, v___x_3656_);
                v___x_3658_ = l_Lean_MessageData_ofFormat(v___x_3657_);
                leanh::lean_inc(v_ref_3655_);
                v___x_3659_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3659_, 0, v_ref_3655_);
                leanh::lean_ctor_set(v___x_3659_, 1, v___x_3658_);
                if v_isShared_3654_ == 0 {
                    leanh::lean_ctor_set(v___x_3653_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3653_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
                    v___x_3661_ = v_reuseFailAlloc_3662_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_3661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_load___boxed(
    mut v_lratPath_3664_: *mut leanh::LeanObject,
    mut v_trimProofs_3665_: *mut leanh::LeanObject,
    mut v_a_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trimProofs_boxed_3669_: u8 = 0;
    let mut v_res_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trimProofs_boxed_3669_ = (leanh::lean_unbox(v_trimProofs_3665_) as u8);
    v_res_3670_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(
        v_lratPath_3664_,
        v_trimProofs_boxed_3669_,
        v_a_3666_,
        v_a_3667_,
    );
    leanh::lean_dec(v_a_3667_);
    leanh::lean_dec_ref(v_a_3666_);
    leanh::lean_dec_ref(v_lratPath_3664_);
    return v_res_3670_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(
    mut v_00_u03b1_3671_: *mut leanh::LeanObject,
    mut v_x_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3676_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_x_3672_);
    return v___x_3676_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___boxed(
    mut v_00_u03b1_3677_: *mut leanh::LeanObject,
    mut v_x_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3682_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6(v_00_u03b1_3677_, v_x_3678_, v___y_3679_, v___y_3680_);
    leanh::lean_dec(v___y_3680_);
    leanh::lean_dec_ref(v___y_3679_);
    return v_res_3682_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(
    mut v_00_u03b1_3683_: *mut leanh::LeanObject,
    mut v_msg_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
    mut v___y_3686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___redArg(
            v_msg_3684_,
            v___y_3685_,
            v___y_3686_,
        );
    return v___x_3688_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5___boxed(
    mut v_00_u03b1_3689_: *mut leanh::LeanObject,
    mut v_msg_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3694_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__5(
        v_00_u03b1_3689_,
        v_msg_3690_,
        v___y_3691_,
        v___y_3692_,
    );
    leanh::lean_dec(v___y_3692_);
    leanh::lean_dec_ref(v___y_3691_);
    return v_res_3694_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
    mut v_lratPath_3695_: *mut leanh::LeanObject,
    mut v_trimProofs_3696_: u8,
    mut v_a_3697_: *mut leanh::LeanObject,
    mut v_a_3698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3700_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load(
                    v_lratPath_3695_,
                    v_trimProofs_3696_,
                    v_a_3697_,
                    v_a_3698_,
                );
                if leanh::lean_obj_tag(v___x_3700_) == 0 {
                    v_a_3701_ = leanh::lean_ctor_get(v___x_3700_, 0);
                    v_isSharedCheck_3709_ = (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                    if v_isSharedCheck_3709_ == 0 {
                        v___x_3703_ = v___x_3700_;
                        v_isShared_3704_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3701_);
                        leanh::lean_dec(v___x_3700_);
                        v___x_3703_ = leanh::lean_box(0);
                        v_isShared_3704_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3710_ = leanh::lean_ctor_get(v___x_3700_, 0);
                    v_isSharedCheck_3717_ = (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3700_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3710_);
                        leanh::lean_dec(v___x_3700_);
                        v___x_3712_ = leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3705_ = l_Std_Tactic_BVDecide_LRAT_lratProofToString(v_a_3701_);
                leanh::lean_dec(v_a_3701_);
                if v_isShared_3704_ == 0 {
                    leanh::lean_ctor_set(v___x_3703_, 0, v___x_3705_);
                    v___x_3707_ = v___x_3703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
                    v___x_3707_ = v_reuseFailAlloc_3708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3707_;
            }
            3 => {
                if v_isShared_3713_ == 0 {
                    v___x_3715_ = v___x_3712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
                    v___x_3715_ = v_reuseFailAlloc_3716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile___boxed(
    mut v_lratPath_3718_: *mut leanh::LeanObject,
    mut v_trimProofs_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trimProofs_boxed_3723_: u8 = 0;
    let mut v_res_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trimProofs_boxed_3723_ = (leanh::lean_unbox(v_trimProofs_3719_) as u8);
    v_res_3724_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
        v_lratPath_3718_,
        v_trimProofs_boxed_3723_,
        v_a_3720_,
        v_a_3721_,
    );
    leanh::lean_dec(v_a_3721_);
    leanh::lean_dec_ref(v_a_3720_);
    leanh::lean_dec_ref(v_lratPath_3718_);
    return v_res_3724_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(
    mut v_snd_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v_a_x3f_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut v_a_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v_ref_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = lean_io_remove_file(v_snd_3725_);
                if leanh::lean_obj_tag(v___x_3729_) == 0 {
                    v_a_3730_ = leanh::lean_ctor_get(v___x_3729_, 0);
                    v_isSharedCheck_3737_ = (!leanh::lean_is_exclusive(v___x_3729_)) as u8;
                    if v_isSharedCheck_3737_ == 0 {
                        v___x_3732_ = v___x_3729_;
                        v_isShared_3733_ = v_isSharedCheck_3737_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3730_);
                        leanh::lean_dec(v___x_3729_);
                        v___x_3732_ = leanh::lean_box(0);
                        v_isShared_3733_ = v_isSharedCheck_3737_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3738_ = leanh::lean_ctor_get(v___x_3729_, 0);
                    v_isSharedCheck_3750_ = (!leanh::lean_is_exclusive(v___x_3729_)) as u8;
                    if v_isSharedCheck_3750_ == 0 {
                        v___x_3740_ = v___x_3729_;
                        v_isShared_3741_ = v_isSharedCheck_3750_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3738_);
                        leanh::lean_dec(v___x_3729_);
                        v___x_3740_ = leanh::lean_box(0);
                        v_isShared_3741_ = v_isSharedCheck_3750_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3733_ == 0 {
                    v___x_3735_ = v___x_3732_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
                    v___x_3735_ = v_reuseFailAlloc_3736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3735_;
            }
            3 => {
                v_ref_3742_ = leanh::lean_ctor_get(v___y_3726_, 5);
                v___x_3743_ = lean_io_error_to_string(v_a_3738_);
                v___x_3744_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3744_, 0, v___x_3743_);
                v___x_3745_ = l_Lean_MessageData_ofFormat(v___x_3744_);
                leanh::lean_inc(v_ref_3742_);
                v___x_3746_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3746_, 0, v_ref_3742_);
                leanh::lean_ctor_set(v___x_3746_, 1, v___x_3745_);
                if v_isShared_3741_ == 0 {
                    leanh::lean_ctor_set(v___x_3740_, 0, v___x_3746_);
                    v___x_3748_ = v___x_3740_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
                    v___x_3748_ = v_reuseFailAlloc_3749_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0___boxed(
    mut v_snd_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v_a_x3f_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3755_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_3751_, v___y_3752_, v_a_x3f_3753_);
    leanh::lean_dec(v_a_x3f_3753_);
    leanh::lean_dec_ref(v___y_3752_);
    leanh::lean_dec_ref(v_snd_3751_);
    return v_res_3755_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(
    mut v_f_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_unused_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_reuseFailAlloc_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_a_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut v_unused_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3808_: u8 = 0;
    let mut v_a_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v_ref_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3760_ = lean_io_create_tempfile();
                if leanh::lean_obj_tag(v___x_3760_) == 0 {
                    v_a_3761_ = leanh::lean_ctor_get(v___x_3760_, 0);
                    leanh::lean_inc(v_a_3761_);
                    leanh::lean_dec_ref_known(v___x_3760_, 1);
                    v_fst_3762_ = leanh::lean_ctor_get(v_a_3761_, 0);
                    leanh::lean_inc(v_fst_3762_);
                    v_snd_3763_ = leanh::lean_ctor_get(v_a_3761_, 1);
                    leanh::lean_inc_n(v_snd_3763_, 2);
                    leanh::lean_dec(v_a_3761_);
                    leanh::lean_inc(v___y_3758_);
                    leanh::lean_inc_ref(v___y_3757_);
                    v_r_3764_ = leanh::lean_apply_5(
                        v_f_3756_,
                        v_fst_3762_,
                        v_snd_3763_,
                        v___y_3757_,
                        v___y_3758_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_3764_) == 0 {
                        v_a_3765_ = leanh::lean_ctor_get(v_r_3764_, 0);
                        v_isSharedCheck_3789_ = (!leanh::lean_is_exclusive(v_r_3764_)) as u8;
                        if v_isSharedCheck_3789_ == 0 {
                            v___x_3767_ = v_r_3764_;
                            v_isShared_3768_ = v_isSharedCheck_3789_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3765_);
                            leanh::lean_dec(v_r_3764_);
                            v___x_3767_ = leanh::lean_box(0);
                            v_isShared_3768_ = v_isSharedCheck_3789_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3790_ = leanh::lean_ctor_get(v_r_3764_, 0);
                        leanh::lean_inc(v_a_3790_);
                        leanh::lean_dec_ref_known(v_r_3764_, 1);
                        v___x_3791_ = leanh::lean_box(0);
                        v___x_3792_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_3763_, v___y_3757_, v___x_3791_);
                        leanh::lean_dec(v_snd_3763_);
                        if leanh::lean_obj_tag(v___x_3792_) == 0 {
                            v_isSharedCheck_3799_ =
                                (!leanh::lean_is_exclusive(v___x_3792_)) as u8;
                            if v_isSharedCheck_3799_ == 0 {
                                v_unused_3800_ = leanh::lean_ctor_get(v___x_3792_, 0);
                                leanh::lean_dec(v_unused_3800_);
                                v___x_3794_ = v___x_3792_;
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3792_);
                                v___x_3794_ = leanh::lean_box(0);
                                v_isShared_3795_ = v_isSharedCheck_3799_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3790_);
                            v_a_3801_ = leanh::lean_ctor_get(v___x_3792_, 0);
                            v_isSharedCheck_3808_ =
                                (!leanh::lean_is_exclusive(v___x_3792_)) as u8;
                            if v_isSharedCheck_3808_ == 0 {
                                v___x_3803_ = v___x_3792_;
                                v_isShared_3804_ = v_isSharedCheck_3808_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3801_);
                                leanh::lean_dec(v___x_3792_);
                                v___x_3803_ = leanh::lean_box(0);
                                v_isShared_3804_ = v_isSharedCheck_3808_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_3756_);
                    v_a_3809_ = leanh::lean_ctor_get(v___x_3760_, 0);
                    v_isSharedCheck_3821_ = (!leanh::lean_is_exclusive(v___x_3760_)) as u8;
                    if v_isSharedCheck_3821_ == 0 {
                        v___x_3811_ = v___x_3760_;
                        v_isShared_3812_ = v_isSharedCheck_3821_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3809_);
                        leanh::lean_dec(v___x_3760_);
                        v___x_3811_ = leanh::lean_box(0);
                        v_isShared_3812_ = v_isSharedCheck_3821_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_3765_);
                if v_isShared_3768_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3767_, 1);
                    v___x_3770_ = v___x_3767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3788_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3765_);
                    v___x_3770_ = v_reuseFailAlloc_3788_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3771_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___lam__0(v_snd_3763_, v___y_3757_, v___x_3770_);
                leanh::lean_dec_ref(v___x_3770_);
                leanh::lean_dec(v_snd_3763_);
                if leanh::lean_obj_tag(v___x_3771_) == 0 {
                    v_isSharedCheck_3778_ = (!leanh::lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v_unused_3779_ = leanh::lean_ctor_get(v___x_3771_, 0);
                        leanh::lean_dec(v_unused_3779_);
                        v___x_3773_ = v___x_3771_;
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3771_);
                        v___x_3773_ = leanh::lean_box(0);
                        v_isShared_3774_ = v_isSharedCheck_3778_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3765_);
                    v_a_3780_ = leanh::lean_ctor_get(v___x_3771_, 0);
                    v_isSharedCheck_3787_ = (!leanh::lean_is_exclusive(v___x_3771_)) as u8;
                    if v_isSharedCheck_3787_ == 0 {
                        v___x_3782_ = v___x_3771_;
                        v_isShared_3783_ = v_isSharedCheck_3787_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3780_);
                        leanh::lean_dec(v___x_3771_);
                        v___x_3782_ = leanh::lean_box(0);
                        v_isShared_3783_ = v_isSharedCheck_3787_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3774_ == 0 {
                    leanh::lean_ctor_set(v___x_3773_, 0, v_a_3765_);
                    v___x_3776_ = v___x_3773_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3777_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_a_3765_);
                    v___x_3776_ = v_reuseFailAlloc_3777_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3776_;
            }
            5 => {
                if v_isShared_3783_ == 0 {
                    v___x_3785_ = v___x_3782_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3785_;
            }
            7 => {
                if v_isShared_3795_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3794_, 1);
                    leanh::lean_ctor_set(v___x_3794_, 0, v_a_3790_);
                    v___x_3797_ = v___x_3794_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3790_);
                    v___x_3797_ = v_reuseFailAlloc_3798_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3797_;
            }
            9 => {
                if v_isShared_3804_ == 0 {
                    v___x_3806_ = v___x_3803_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3806_;
            }
            11 => {
                v_ref_3813_ = leanh::lean_ctor_get(v___y_3757_, 5);
                v___x_3814_ = lean_io_error_to_string(v_a_3809_);
                v___x_3815_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3815_, 0, v___x_3814_);
                v___x_3816_ = l_Lean_MessageData_ofFormat(v___x_3815_);
                leanh::lean_inc(v_ref_3813_);
                v___x_3817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3817_, 0, v_ref_3813_);
                leanh::lean_ctor_set(v___x_3817_, 1, v___x_3816_);
                if v_isShared_3812_ == 0 {
                    leanh::lean_ctor_set(v___x_3811_, 0, v___x_3817_);
                    v___x_3819_ = v___x_3811_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3820_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
                    v___x_3819_ = v_reuseFailAlloc_3820_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg___boxed(
    mut v_f_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3826_ =
        l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(
            v_f_3822_,
            v___y_3823_,
            v___y_3824_,
        );
    leanh::lean_dec(v___y_3824_);
    leanh::lean_dec_ref(v___y_3823_);
    return v_res_3826_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(
    mut v_00_u03b1_3827_: *mut leanh::LeanObject,
    mut v_f_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
    mut v___y_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3832_ =
        l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(
            v_f_3828_,
            v___y_3829_,
            v___y_3830_,
        );
    return v___x_3832_;
}
pub unsafe fn l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___boxed(
    mut v_00_u03b1_3833_: *mut leanh::LeanObject,
    mut v_f_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3(
        v_00_u03b1_3833_,
        v_f_3834_,
        v___y_3835_,
        v___y_3836_,
    );
    leanh::lean_dec(v___y_3836_);
    leanh::lean_dec_ref(v___y_3835_);
    return v_res_3838_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(
    mut v_cnf_3839_: *mut leanh::LeanObject,
    mut v_x_3840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Std_Sat_CNF_dimacs(v_cnf_3839_);
    return v___x_3841_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed(
    mut v_cnf_3842_: *mut leanh::LeanObject,
    mut v_x_3843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3844_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0(v_cnf_3842_, v_x_3843_);
    leanh::lean_dec_ref(v_cnf_3842_);
    return v_res_3844_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3848_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__1;
    v___x_3849_ = l_Lean_MessageData_ofFormat(v___x_3848_);
    return v___x_3849_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(
    mut v_x_3850_: *mut leanh::LeanObject,
    mut v___y_3851_: *mut leanh::LeanObject,
    mut v___y_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___closed__2,
    );
    v___x_3855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3855_, 0, v___x_3854_);
    return v___x_3855_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1___boxed(
    mut v_x_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ =
        l_Lean_Meta_Tactic_BVDecide_runExternal___lam__1(v_x_3856_, v___y_3857_, v___y_3858_);
    leanh::lean_dec(v___y_3858_);
    leanh::lean_dec_ref(v___y_3857_);
    leanh::lean_dec_ref(v_x_3856_);
    return v_res_3860_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__1;
    v___x_3865_ = l_Lean_MessageData_ofFormat(v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(
    mut v_x_3866_: *mut leanh::LeanObject,
    mut v___y_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___closed__2,
    );
    v___x_3871_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3871_, 0, v___x_3870_);
    return v___x_3871_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2___boxed(
    mut v_x_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ =
        l_Lean_Meta_Tactic_BVDecide_runExternal___lam__2(v_x_3872_, v___y_3873_, v___y_3874_);
    leanh::lean_dec(v___y_3874_);
    leanh::lean_dec_ref(v___y_3873_);
    leanh::lean_dec_ref(v_x_3872_);
    return v_res_3876_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__1;
    v___x_3881_ = l_Lean_MessageData_ofFormat(v___x_3880_);
    return v___x_3881_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(
    mut v_x_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2_once),
        _init_l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___closed__2,
    );
    v___x_3887_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3887_, 0, v___x_3886_);
    return v___x_3887_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3___boxed(
    mut v_x_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3892_ =
        l_Lean_Meta_Tactic_BVDecide_runExternal___lam__3(v_x_3888_, v___y_3889_, v___y_3890_);
    leanh::lean_dec(v___y_3890_);
    leanh::lean_dec_ref(v___y_3889_);
    leanh::lean_dec_ref(v_x_3888_);
    return v_res_3892_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(
    mut v_e_3893_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_3893_) == 0 {
        let mut v___x_3894_: u8 = 0;
        v___x_3894_ = 2;
        return v___x_3894_;
    } else {
        let mut v___x_3895_: u8 = 0;
        v___x_3895_ = 0;
        return v___x_3895_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4___boxed(
    mut v_e_3896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3897_: u8 = 0;
    let mut v_r_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3897_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_e_3896_);
    leanh::lean_dec_ref(v_e_3896_);
    v_r_3898_ = leanh::lean_box((v_res_3897_) as usize);
    return v_r_3898_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(
    mut v_cls_3899_: *mut leanh::LeanObject,
    mut v_collapsed_3900_: u8,
    mut v_tag_3901_: *mut leanh::LeanObject,
    mut v_opts_3902_: *mut leanh::LeanObject,
    mut v_clsEnabled_3903_: u8,
    mut v_oldTraces_3904_: *mut leanh::LeanObject,
    mut v_msg_3905_: *mut leanh::LeanObject,
    mut v_resStartStop_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___y_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___y_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_3931_: u8 = 0;
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: f64 = 0.0;
    let mut v_data_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: f64 = 0.0;
    let mut v___x_3945_: f64 = 0.0;
    let mut v_reuseFailAlloc_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: u8 = 0;
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v_tid_3968_: u64 = 0;
    let mut v_traces_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3982_: u8 = 0;
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v___y_3985_: f64 = 0.0;
    let mut v___x_3986_: f64 = 0.0;
    let mut v___x_3987_: f64 = 0.0;
    let mut v___x_3988_: f64 = 0.0;
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: f64 = 0.0;
    let mut v___x_3995_: f64 = 0.0;
    let mut v___x_3996_: f64 = 0.0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: f64 = 0.0;
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3910_ = leanh::lean_ctor_get(v_resStartStop_3906_, 0);
                v_snd_3911_ = leanh::lean_ctor_get(v_resStartStop_3906_, 1);
                v_isSharedCheck_4001_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_3906_)) as u8;
                if v_isSharedCheck_4001_ == 0 {
                    v___x_3913_ = v_resStartStop_3906_;
                    v_isShared_3914_ = v_isSharedCheck_4001_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3911_);
                    leanh::lean_inc(v_fst_3910_);
                    leanh::lean_dec(v_resStartStop_3906_);
                    v___x_3913_ = leanh::lean_box(0);
                    v_isShared_3914_ = v_isSharedCheck_4001_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3921_ = leanh::lean_ctor_get(v_snd_3911_, 0);
                v_snd_3922_ = leanh::lean_ctor_get(v_snd_3911_, 1);
                v_isSharedCheck_4000_ = (!leanh::lean_is_exclusive(v_snd_3911_)) as u8;
                if v_isSharedCheck_4000_ == 0 {
                    v___x_3924_ = v_snd_3911_;
                    v_isShared_3925_ = v_isSharedCheck_4000_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3922_);
                    leanh::lean_inc(v_fst_3921_);
                    leanh::lean_dec(v_snd_3911_);
                    v___x_3924_ = leanh::lean_box(0);
                    v_isShared_3925_ = v_isSharedCheck_4000_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_3917_);
                v___x_3919_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_3904_, v_data_3918_, v___y_3917_, v___y_3916_, v___y_3907_, v___y_3908_);
                if leanh::lean_obj_tag(v___x_3919_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3919_, 1);
                    v___x_3920_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_3910_);
                    return v___x_3920_;
                } else {
                    leanh::lean_dec(v_fst_3910_);
                    return v___x_3919_;
                }
            }
            3 => {
                v___x_3926_ = l_Lean_trace_profiler;
                v___x_3927_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_opts_3902_,
                        v___x_3926_,
                    );
                if v___x_3927_ == 0 {
                    v___y_3954_ = v___x_3927_;
                    state = 8;
                    continue;
                } else {
                    v___x_3990_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_3991_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                            v_opts_3902_,
                            v___x_3990_,
                        );
                    if v___x_3991_ == 0 {
                        v___x_3992_ = l_Lean_trace_profiler_threshold;
                        v___x_3993_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_3902_, v___x_3992_);
                        v___x_3994_ = lean_float_of_nat(v___x_3993_);
                        v___x_3995_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
                        v___x_3996_ = lean_float_div(v___x_3994_, v___x_3995_);
                        v___y_3985_ = v___x_3996_;
                        state = 13;
                        continue;
                    } else {
                        v___x_3997_ = l_Lean_trace_profiler_threshold;
                        v___x_3998_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_3902_, v___x_3997_);
                        v___x_3999_ = lean_float_of_nat(v___x_3998_);
                        v___y_3985_ = v___x_3999_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_result_3931_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2_spec__4(v_fst_3910_);
                v___x_3932_ = l_Lean_TraceResult_toEmoji(v_result_3931_);
                v___x_3933_ = l_Lean_stringToMessageData(v___x_3932_);
                v___x_3934_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
                if v_isShared_3925_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3924_, 7);
                    leanh::lean_ctor_set(v___x_3924_, 1, v___x_3934_);
                    leanh::lean_ctor_set(v___x_3924_, 0, v___x_3933_);
                    v___x_3936_ = v___x_3924_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3947_, 1, v___x_3934_);
                    v___x_3936_ = v_reuseFailAlloc_3947_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3914_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3913_, 7);
                    leanh::lean_ctor_set(v___x_3913_, 1, v_a_3930_);
                    leanh::lean_ctor_set(v___x_3913_, 0, v___x_3936_);
                    v_m_3938_ = v___x_3913_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3946_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_a_3930_);
                    v_m_3938_ = v_reuseFailAlloc_3946_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3939_ = leanh::lean_box((v_result_3931_) as usize);
                v___x_3940_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3940_, 0, v___x_3939_);
                v___x_3941_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
                leanh::lean_inc_ref(v_tag_3901_);
                leanh::lean_inc_ref(v___x_3940_);
                leanh::lean_inc(v_cls_3899_);
                v_data_3942_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_3942_, 0, v_cls_3899_);
                leanh::lean_ctor_set(v_data_3942_, 1, v___x_3940_);
                leanh::lean_ctor_set(v_data_3942_, 2, v_tag_3901_);
                leanh::lean_ctor_set_float(
                    v_data_3942_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_3941_,
                );
                leanh::lean_ctor_set_float(
                    v_data_3942_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3941_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_3942_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_3900_,
                );
                if v___x_3927_ == 0 {
                    leanh::lean_dec_ref_known(v___x_3940_, 1);
                    leanh::lean_dec(v_snd_3922_);
                    leanh::lean_dec(v_fst_3921_);
                    leanh::lean_dec_ref(v_tag_3901_);
                    leanh::lean_dec(v_cls_3899_);
                    v___y_3916_ = v_m_3938_;
                    v___y_3917_ = v___y_3929_;
                    v_data_3918_ = v_data_3942_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_3942_, 3);
                    v_data_3943_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_3943_, 0, v_cls_3899_);
                    leanh::lean_ctor_set(v_data_3943_, 1, v___x_3940_);
                    leanh::lean_ctor_set(v_data_3943_, 2, v_tag_3901_);
                    v___x_3944_ = leanh::lean_unbox_float(v_fst_3921_);
                    leanh::lean_dec(v_fst_3921_);
                    leanh::lean_ctor_set_float(
                        v_data_3943_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_3944_,
                    );
                    v___x_3945_ = leanh::lean_unbox_float(v_snd_3922_);
                    leanh::lean_dec(v_snd_3922_);
                    leanh::lean_ctor_set_float(
                        v_data_3943_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_3945_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_3943_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_3900_,
                    );
                    v___y_3916_ = v_m_3938_;
                    v___y_3917_ = v___y_3929_;
                    v_data_3918_ = v_data_3943_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                v_ref_3949_ = leanh::lean_ctor_get(v___y_3907_, 5);
                leanh::lean_inc(v___y_3908_);
                leanh::lean_inc_ref(v___y_3907_);
                leanh::lean_inc(v_fst_3910_);
                v___x_3950_ = leanh::lean_apply_4(
                    v_msg_3905_,
                    v_fst_3910_,
                    v___y_3907_,
                    v___y_3908_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3950_) == 0 {
                    v_a_3951_ = leanh::lean_ctor_get(v___x_3950_, 0);
                    leanh::lean_inc(v_a_3951_);
                    leanh::lean_dec_ref_known(v___x_3950_, 1);
                    v___y_3929_ = v_ref_3949_;
                    v_a_3930_ = v_a_3951_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_3950_, 1);
                    v___x_3952_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
                    v___y_3929_ = v_ref_3949_;
                    v_a_3930_ = v___x_3952_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                if v_clsEnabled_3903_ == 0 {
                    if v___y_3954_ == 0 {
                        leanh::lean_del_object(v___x_3924_);
                        leanh::lean_dec(v_snd_3922_);
                        leanh::lean_dec(v_fst_3921_);
                        leanh::lean_del_object(v___x_3913_);
                        leanh::lean_dec_ref(v_msg_3905_);
                        leanh::lean_dec_ref(v_tag_3901_);
                        leanh::lean_dec(v_cls_3899_);
                        v___x_3955_ = lean_st_ref_take(v___y_3908_);
                        v_traceState_3956_ = leanh::lean_ctor_get(v___x_3955_, 4);
                        v_env_3957_ = leanh::lean_ctor_get(v___x_3955_, 0);
                        v_nextMacroScope_3958_ = leanh::lean_ctor_get(v___x_3955_, 1);
                        v_ngen_3959_ = leanh::lean_ctor_get(v___x_3955_, 2);
                        v_auxDeclNGen_3960_ = leanh::lean_ctor_get(v___x_3955_, 3);
                        v_cache_3961_ = leanh::lean_ctor_get(v___x_3955_, 5);
                        v_messages_3962_ = leanh::lean_ctor_get(v___x_3955_, 6);
                        v_infoState_3963_ = leanh::lean_ctor_get(v___x_3955_, 7);
                        v_snapshotTasks_3964_ = leanh::lean_ctor_get(v___x_3955_, 8);
                        v_isSharedCheck_3983_ =
                            (!leanh::lean_is_exclusive(v___x_3955_)) as u8;
                        if v_isSharedCheck_3983_ == 0 {
                            v___x_3966_ = v___x_3955_;
                            v_isShared_3967_ = v_isSharedCheck_3983_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_3964_);
                            leanh::lean_inc(v_infoState_3963_);
                            leanh::lean_inc(v_messages_3962_);
                            leanh::lean_inc(v_cache_3961_);
                            leanh::lean_inc(v_traceState_3956_);
                            leanh::lean_inc(v_auxDeclNGen_3960_);
                            leanh::lean_inc(v_ngen_3959_);
                            leanh::lean_inc(v_nextMacroScope_3958_);
                            leanh::lean_inc(v_env_3957_);
                            leanh::lean_dec(v___x_3955_);
                            v___x_3966_ = leanh::lean_box(0);
                            v_isShared_3967_ = v_isSharedCheck_3983_;
                            state = 9;
                            continue;
                        }
                    } else {
                        state = 7;
                        continue;
                    }
                } else {
                    state = 7;
                    continue;
                }
            }
            9 => {
                v_tid_3968_ = leanh::lean_ctor_get_uint64(
                    v_traceState_3956_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3969_ = leanh::lean_ctor_get(v_traceState_3956_, 0);
                v_isSharedCheck_3982_ =
                    (!leanh::lean_is_exclusive(v_traceState_3956_)) as u8;
                if v_isSharedCheck_3982_ == 0 {
                    v___x_3971_ = v_traceState_3956_;
                    v_isShared_3972_ = v_isSharedCheck_3982_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_3969_);
                    leanh::lean_dec(v_traceState_3956_);
                    v___x_3971_ = leanh::lean_box(0);
                    v_isShared_3972_ = v_isSharedCheck_3982_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3973_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_3904_, v_traces_3969_);
                leanh::lean_dec_ref(v_traces_3969_);
                if v_isShared_3972_ == 0 {
                    leanh::lean_ctor_set(v___x_3971_, 0, v___x_3973_);
                    v___x_3975_ = v___x_3971_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3973_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3981_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_3968_,
                    );
                    v___x_3975_ = v_reuseFailAlloc_3981_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3967_ == 0 {
                    leanh::lean_ctor_set(v___x_3966_, 4, v___x_3975_);
                    v___x_3977_ = v___x_3966_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3980_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_env_3957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 1, v_nextMacroScope_3958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_ngen_3959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_auxDeclNGen_3960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 4, v___x_3975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 5, v_cache_3961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 6, v_messages_3962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 7, v_infoState_3963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3980_, 8, v_snapshotTasks_3964_);
                    v___x_3977_ = v_reuseFailAlloc_3980_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3978_ = lean_st_ref_set(v___y_3908_, v___x_3977_);
                v___x_3979_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_3910_);
                return v___x_3979_;
            }
            13 => {
                v___x_3986_ = leanh::lean_unbox_float(v_snd_3922_);
                v___x_3987_ = leanh::lean_unbox_float(v_fst_3921_);
                v___x_3988_ = lean_float_sub(v___x_3986_, v___x_3987_);
                v___x_3989_ = lean_float_decLt(v___y_3985_, v___x_3988_);
                v___y_3954_ = v___x_3989_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2___boxed(
    mut v_cls_4002_: *mut leanh::LeanObject,
    mut v_collapsed_4003_: *mut leanh::LeanObject,
    mut v_tag_4004_: *mut leanh::LeanObject,
    mut v_opts_4005_: *mut leanh::LeanObject,
    mut v_clsEnabled_4006_: *mut leanh::LeanObject,
    mut v_oldTraces_4007_: *mut leanh::LeanObject,
    mut v_msg_4008_: *mut leanh::LeanObject,
    mut v_resStartStop_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_4013_: u8 = 0;
    let mut v_clsEnabled_boxed_4014_: u8 = 0;
    let mut v_res_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4013_ = (leanh::lean_unbox(v_collapsed_4003_) as u8);
    v_clsEnabled_boxed_4014_ = (leanh::lean_unbox(v_clsEnabled_4006_) as u8);
    v_res_4015_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v_cls_4002_, v_collapsed_boxed_4013_, v_tag_4004_, v_opts_4005_, v_clsEnabled_boxed_4014_, v_oldTraces_4007_, v_msg_4008_, v_resStartStop_4009_, v___y_4010_, v___y_4011_);
    leanh::lean_dec(v___y_4011_);
    leanh::lean_dec_ref(v___y_4010_);
    leanh::lean_dec_ref(v_opts_4005_);
    return v_res_4015_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(
    mut v_e_4016_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_4016_) == 0 {
        let mut v___x_4017_: u8 = 0;
        v___x_4017_ = 2;
        return v___x_4017_;
    } else {
        let mut v___x_4018_: u8 = 0;
        v___x_4018_ = 0;
        return v___x_4018_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0___boxed(
    mut v_e_4019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4020_: u8 = 0;
    let mut v_r_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4020_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_e_4019_);
    leanh::lean_dec_ref(v_e_4019_);
    v_r_4021_ = leanh::lean_box((v_res_4020_) as usize);
    return v_r_4021_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(
    mut v_cls_4022_: *mut leanh::LeanObject,
    mut v_collapsed_4023_: u8,
    mut v_tag_4024_: *mut leanh::LeanObject,
    mut v_opts_4025_: *mut leanh::LeanObject,
    mut v_clsEnabled_4026_: u8,
    mut v_oldTraces_4027_: *mut leanh::LeanObject,
    mut v_msg_4028_: *mut leanh::LeanObject,
    mut v_resStartStop_4029_: *mut leanh::LeanObject,
    mut v___y_4030_: *mut leanh::LeanObject,
    mut v___y_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v___y_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4047_: u8 = 0;
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4051_: u8 = 0;
    let mut v_fst_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: u8 = 0;
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_4062_: u8 = 0;
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: f64 = 0.0;
    let mut v_data_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: f64 = 0.0;
    let mut v___x_4076_: f64 = 0.0;
    let mut v_reuseFailAlloc_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: u8 = 0;
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4098_: u8 = 0;
    let mut v_tid_4099_: u64 = 0;
    let mut v_traces_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v___y_4116_: f64 = 0.0;
    let mut v___x_4117_: f64 = 0.0;
    let mut v___x_4118_: f64 = 0.0;
    let mut v___x_4119_: f64 = 0.0;
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: f64 = 0.0;
    let mut v___x_4126_: f64 = 0.0;
    let mut v___x_4127_: f64 = 0.0;
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: f64 = 0.0;
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4033_ = leanh::lean_ctor_get(v_resStartStop_4029_, 0);
                v_snd_4034_ = leanh::lean_ctor_get(v_resStartStop_4029_, 1);
                v_isSharedCheck_4132_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_4029_)) as u8;
                if v_isSharedCheck_4132_ == 0 {
                    v___x_4036_ = v_resStartStop_4029_;
                    v_isShared_4037_ = v_isSharedCheck_4132_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4034_);
                    leanh::lean_inc(v_fst_4033_);
                    leanh::lean_dec(v_resStartStop_4029_);
                    v___x_4036_ = leanh::lean_box(0);
                    v_isShared_4037_ = v_isSharedCheck_4132_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4052_ = leanh::lean_ctor_get(v_snd_4034_, 0);
                v_snd_4053_ = leanh::lean_ctor_get(v_snd_4034_, 1);
                v_isSharedCheck_4131_ = (!leanh::lean_is_exclusive(v_snd_4034_)) as u8;
                if v_isSharedCheck_4131_ == 0 {
                    v___x_4055_ = v_snd_4034_;
                    v_isShared_4056_ = v_isSharedCheck_4131_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4053_);
                    leanh::lean_inc(v_fst_4052_);
                    leanh::lean_dec(v_snd_4034_);
                    v___x_4055_ = leanh::lean_box(0);
                    v_isShared_4056_ = v_isSharedCheck_4131_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_4040_);
                v___x_4042_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_4027_, v_data_4041_, v___y_4040_, v___y_4039_, v___y_4030_, v___y_4031_);
                if leanh::lean_obj_tag(v___x_4042_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4042_, 1);
                    v___x_4043_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_4033_);
                    return v___x_4043_;
                } else {
                    leanh::lean_dec(v_fst_4033_);
                    v_a_4044_ = leanh::lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4051_ = (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4051_ == 0 {
                        v___x_4046_ = v___x_4042_;
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4044_);
                        leanh::lean_dec(v___x_4042_);
                        v___x_4046_ = leanh::lean_box(0);
                        v_isShared_4047_ = v_isSharedCheck_4051_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4047_ == 0 {
                    v___x_4049_ = v___x_4046_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
                    v___x_4049_ = v_reuseFailAlloc_4050_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4049_;
            }
            5 => {
                v___x_4057_ = l_Lean_trace_profiler;
                v___x_4058_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_opts_4025_,
                        v___x_4057_,
                    );
                if v___x_4058_ == 0 {
                    v___y_4085_ = v___x_4058_;
                    state = 10;
                    continue;
                } else {
                    v___x_4121_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_4122_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                            v_opts_4025_,
                            v___x_4121_,
                        );
                    if v___x_4122_ == 0 {
                        v___x_4123_ = l_Lean_trace_profiler_threshold;
                        v___x_4124_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_4025_, v___x_4123_);
                        v___x_4125_ = lean_float_of_nat(v___x_4124_);
                        v___x_4126_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
                        v___x_4127_ = lean_float_div(v___x_4125_, v___x_4126_);
                        v___y_4116_ = v___x_4127_;
                        state = 15;
                        continue;
                    } else {
                        v___x_4128_ = l_Lean_trace_profiler_threshold;
                        v___x_4129_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_4025_, v___x_4128_);
                        v___x_4130_ = lean_float_of_nat(v___x_4129_);
                        v___y_4116_ = v___x_4130_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_4062_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0_spec__0(v_fst_4033_);
                v___x_4063_ = l_Lean_TraceResult_toEmoji(v_result_4062_);
                v___x_4064_ = l_Lean_stringToMessageData(v___x_4063_);
                v___x_4065_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
                if v_isShared_4056_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4055_, 7);
                    leanh::lean_ctor_set(v___x_4055_, 1, v___x_4065_);
                    leanh::lean_ctor_set(v___x_4055_, 0, v___x_4064_);
                    v___x_4067_ = v___x_4055_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4078_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 1, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4078_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4037_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4036_, 7);
                    leanh::lean_ctor_set(v___x_4036_, 1, v_a_4061_);
                    leanh::lean_ctor_set(v___x_4036_, 0, v___x_4067_);
                    v_m_4069_ = v___x_4036_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_a_4061_);
                    v_m_4069_ = v_reuseFailAlloc_4077_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4070_ = leanh::lean_box((v_result_4062_) as usize);
                v___x_4071_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4071_, 0, v___x_4070_);
                v___x_4072_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
                leanh::lean_inc_ref(v_tag_4024_);
                leanh::lean_inc_ref(v___x_4071_);
                leanh::lean_inc(v_cls_4022_);
                v_data_4073_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_4073_, 0, v_cls_4022_);
                leanh::lean_ctor_set(v_data_4073_, 1, v___x_4071_);
                leanh::lean_ctor_set(v_data_4073_, 2, v_tag_4024_);
                leanh::lean_ctor_set_float(
                    v_data_4073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4072_,
                );
                leanh::lean_ctor_set_float(
                    v_data_4073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4072_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_4073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_4023_,
                );
                if v___x_4058_ == 0 {
                    leanh::lean_dec_ref_known(v___x_4071_, 1);
                    leanh::lean_dec(v_snd_4053_);
                    leanh::lean_dec(v_fst_4052_);
                    leanh::lean_dec_ref(v_tag_4024_);
                    leanh::lean_dec(v_cls_4022_);
                    v___y_4039_ = v_m_4069_;
                    v___y_4040_ = v___y_4060_;
                    v_data_4041_ = v_data_4073_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_4073_, 3);
                    v_data_4074_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_4074_, 0, v_cls_4022_);
                    leanh::lean_ctor_set(v_data_4074_, 1, v___x_4071_);
                    leanh::lean_ctor_set(v_data_4074_, 2, v_tag_4024_);
                    v___x_4075_ = leanh::lean_unbox_float(v_fst_4052_);
                    leanh::lean_dec(v_fst_4052_);
                    leanh::lean_ctor_set_float(
                        v_data_4074_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_4075_,
                    );
                    v___x_4076_ = leanh::lean_unbox_float(v_snd_4053_);
                    leanh::lean_dec(v_snd_4053_);
                    leanh::lean_ctor_set_float(
                        v_data_4074_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_4076_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_4074_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_4023_,
                    );
                    v___y_4039_ = v_m_4069_;
                    v___y_4040_ = v___y_4060_;
                    v_data_4041_ = v_data_4074_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_4080_ = leanh::lean_ctor_get(v___y_4030_, 5);
                leanh::lean_inc(v___y_4031_);
                leanh::lean_inc_ref(v___y_4030_);
                leanh::lean_inc(v_fst_4033_);
                v___x_4081_ = leanh::lean_apply_4(
                    v_msg_4028_,
                    v_fst_4033_,
                    v___y_4030_,
                    v___y_4031_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4081_) == 0 {
                    v_a_4082_ = leanh::lean_ctor_get(v___x_4081_, 0);
                    leanh::lean_inc(v_a_4082_);
                    leanh::lean_dec_ref_known(v___x_4081_, 1);
                    v___y_4060_ = v_ref_4080_;
                    v_a_4061_ = v_a_4082_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_4081_, 1);
                    v___x_4083_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
                    v___y_4060_ = v_ref_4080_;
                    v_a_4061_ = v___x_4083_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_4026_ == 0 {
                    if v___y_4085_ == 0 {
                        leanh::lean_del_object(v___x_4055_);
                        leanh::lean_dec(v_snd_4053_);
                        leanh::lean_dec(v_fst_4052_);
                        leanh::lean_del_object(v___x_4036_);
                        leanh::lean_dec_ref(v_msg_4028_);
                        leanh::lean_dec_ref(v_tag_4024_);
                        leanh::lean_dec(v_cls_4022_);
                        v___x_4086_ = lean_st_ref_take(v___y_4031_);
                        v_traceState_4087_ = leanh::lean_ctor_get(v___x_4086_, 4);
                        v_env_4088_ = leanh::lean_ctor_get(v___x_4086_, 0);
                        v_nextMacroScope_4089_ = leanh::lean_ctor_get(v___x_4086_, 1);
                        v_ngen_4090_ = leanh::lean_ctor_get(v___x_4086_, 2);
                        v_auxDeclNGen_4091_ = leanh::lean_ctor_get(v___x_4086_, 3);
                        v_cache_4092_ = leanh::lean_ctor_get(v___x_4086_, 5);
                        v_messages_4093_ = leanh::lean_ctor_get(v___x_4086_, 6);
                        v_infoState_4094_ = leanh::lean_ctor_get(v___x_4086_, 7);
                        v_snapshotTasks_4095_ = leanh::lean_ctor_get(v___x_4086_, 8);
                        v_isSharedCheck_4114_ =
                            (!leanh::lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4114_ == 0 {
                            v___x_4097_ = v___x_4086_;
                            v_isShared_4098_ = v_isSharedCheck_4114_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_4095_);
                            leanh::lean_inc(v_infoState_4094_);
                            leanh::lean_inc(v_messages_4093_);
                            leanh::lean_inc(v_cache_4092_);
                            leanh::lean_inc(v_traceState_4087_);
                            leanh::lean_inc(v_auxDeclNGen_4091_);
                            leanh::lean_inc(v_ngen_4090_);
                            leanh::lean_inc(v_nextMacroScope_4089_);
                            leanh::lean_inc(v_env_4088_);
                            leanh::lean_dec(v___x_4086_);
                            v___x_4097_ = leanh::lean_box(0);
                            v_isShared_4098_ = v_isSharedCheck_4114_;
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
                v_tid_4099_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4087_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4100_ = leanh::lean_ctor_get(v_traceState_4087_, 0);
                v_isSharedCheck_4113_ =
                    (!leanh::lean_is_exclusive(v_traceState_4087_)) as u8;
                if v_isSharedCheck_4113_ == 0 {
                    v___x_4102_ = v_traceState_4087_;
                    v_isShared_4103_ = v_isSharedCheck_4113_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4100_);
                    leanh::lean_dec(v_traceState_4087_);
                    v___x_4102_ = leanh::lean_box(0);
                    v_isShared_4103_ = v_isSharedCheck_4113_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4104_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_4027_, v_traces_4100_);
                leanh::lean_dec_ref(v_traces_4100_);
                if v_isShared_4103_ == 0 {
                    leanh::lean_ctor_set(v___x_4102_, 0, v___x_4104_);
                    v___x_4106_ = v___x_4102_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4112_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4104_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4112_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4099_,
                    );
                    v___x_4106_ = v_reuseFailAlloc_4112_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4098_ == 0 {
                    leanh::lean_ctor_set(v___x_4097_, 4, v___x_4106_);
                    v___x_4108_ = v___x_4097_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4111_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_env_4088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_nextMacroScope_4089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_ngen_4090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 3, v_auxDeclNGen_4091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 4, v___x_4106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 5, v_cache_4092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 6, v_messages_4093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 7, v_infoState_4094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4111_, 8, v_snapshotTasks_4095_);
                    v___x_4108_ = v_reuseFailAlloc_4111_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4109_ = lean_st_ref_set(v___y_4031_, v___x_4108_);
                v___x_4110_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_4033_);
                return v___x_4110_;
            }
            15 => {
                v___x_4117_ = leanh::lean_unbox_float(v_snd_4053_);
                v___x_4118_ = leanh::lean_unbox_float(v_fst_4052_);
                v___x_4119_ = lean_float_sub(v___x_4117_, v___x_4118_);
                v___x_4120_ = lean_float_decLt(v___y_4116_, v___x_4119_);
                v___y_4085_ = v___x_4120_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0___boxed(
    mut v_cls_4133_: *mut leanh::LeanObject,
    mut v_collapsed_4134_: *mut leanh::LeanObject,
    mut v_tag_4135_: *mut leanh::LeanObject,
    mut v_opts_4136_: *mut leanh::LeanObject,
    mut v_clsEnabled_4137_: *mut leanh::LeanObject,
    mut v_oldTraces_4138_: *mut leanh::LeanObject,
    mut v_msg_4139_: *mut leanh::LeanObject,
    mut v_resStartStop_4140_: *mut leanh::LeanObject,
    mut v___y_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_4144_: u8 = 0;
    let mut v_clsEnabled_boxed_4145_: u8 = 0;
    let mut v_res_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4144_ = (leanh::lean_unbox(v_collapsed_4134_) as u8);
    v_clsEnabled_boxed_4145_ = (leanh::lean_unbox(v_clsEnabled_4137_) as u8);
    v_res_4146_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v_cls_4133_, v_collapsed_boxed_4144_, v_tag_4135_, v_opts_4136_, v_clsEnabled_boxed_4145_, v_oldTraces_4138_, v_msg_4139_, v_resStartStop_4140_, v___y_4141_, v___y_4142_);
    leanh::lean_dec(v___y_4142_);
    leanh::lean_dec_ref(v___y_4141_);
    leanh::lean_dec_ref(v_opts_4136_);
    return v_res_4146_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(
    mut v_e_4147_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_4147_) == 0 {
        let mut v___x_4148_: u8 = 0;
        v___x_4148_ = 2;
        return v___x_4148_;
    } else {
        let mut v___x_4149_: u8 = 0;
        v___x_4149_ = 0;
        return v___x_4149_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2___boxed(
    mut v_e_4150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4151_: u8 = 0;
    let mut v_r_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4151_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_e_4150_);
    leanh::lean_dec_ref(v_e_4150_);
    v_r_4152_ = leanh::lean_box((v_res_4151_) as usize);
    return v_r_4152_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(
    mut v_cls_4153_: *mut leanh::LeanObject,
    mut v_collapsed_4154_: u8,
    mut v_tag_4155_: *mut leanh::LeanObject,
    mut v_opts_4156_: *mut leanh::LeanObject,
    mut v_clsEnabled_4157_: u8,
    mut v_oldTraces_4158_: *mut leanh::LeanObject,
    mut v_msg_4159_: *mut leanh::LeanObject,
    mut v_resStartStop_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___y_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v_fst_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___y_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_4193_: u8 = 0;
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: f64 = 0.0;
    let mut v_data_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: f64 = 0.0;
    let mut v___x_4207_: f64 = 0.0;
    let mut v_reuseFailAlloc_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: u8 = 0;
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v_tid_4230_: u64 = 0;
    let mut v_traces_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v___y_4247_: f64 = 0.0;
    let mut v___x_4248_: f64 = 0.0;
    let mut v___x_4249_: f64 = 0.0;
    let mut v___x_4250_: f64 = 0.0;
    let mut v___x_4251_: u8 = 0;
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: f64 = 0.0;
    let mut v___x_4257_: f64 = 0.0;
    let mut v___x_4258_: f64 = 0.0;
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: f64 = 0.0;
    let mut v_isSharedCheck_4262_: u8 = 0;
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4164_ = leanh::lean_ctor_get(v_resStartStop_4160_, 0);
                v_snd_4165_ = leanh::lean_ctor_get(v_resStartStop_4160_, 1);
                v_isSharedCheck_4263_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_4160_)) as u8;
                if v_isSharedCheck_4263_ == 0 {
                    v___x_4167_ = v_resStartStop_4160_;
                    v_isShared_4168_ = v_isSharedCheck_4263_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4165_);
                    leanh::lean_inc(v_fst_4164_);
                    leanh::lean_dec(v_resStartStop_4160_);
                    v___x_4167_ = leanh::lean_box(0);
                    v_isShared_4168_ = v_isSharedCheck_4263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_4183_ = leanh::lean_ctor_get(v_snd_4165_, 0);
                v_snd_4184_ = leanh::lean_ctor_get(v_snd_4165_, 1);
                v_isSharedCheck_4262_ = (!leanh::lean_is_exclusive(v_snd_4165_)) as u8;
                if v_isSharedCheck_4262_ == 0 {
                    v___x_4186_ = v_snd_4165_;
                    v_isShared_4187_ = v_isSharedCheck_4262_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4184_);
                    leanh::lean_inc(v_fst_4183_);
                    leanh::lean_dec(v_snd_4165_);
                    v___x_4186_ = leanh::lean_box(0);
                    v_isShared_4187_ = v_isSharedCheck_4262_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_4171_);
                v___x_4173_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__5(v_oldTraces_4158_, v_data_4172_, v___y_4171_, v___y_4170_, v___y_4161_, v___y_4162_);
                if leanh::lean_obj_tag(v___x_4173_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4173_, 1);
                    v___x_4174_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_4164_);
                    return v___x_4174_;
                } else {
                    leanh::lean_dec(v_fst_4164_);
                    v_a_4175_ = leanh::lean_ctor_get(v___x_4173_, 0);
                    v_isSharedCheck_4182_ = (!leanh::lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4182_ == 0 {
                        v___x_4177_ = v___x_4173_;
                        v_isShared_4178_ = v_isSharedCheck_4182_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4175_);
                        leanh::lean_dec(v___x_4173_);
                        v___x_4177_ = leanh::lean_box(0);
                        v_isShared_4178_ = v_isSharedCheck_4182_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4178_ == 0 {
                    v___x_4180_ = v___x_4177_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4180_;
            }
            5 => {
                v___x_4188_ = l_Lean_trace_profiler;
                v___x_4189_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_opts_4156_,
                        v___x_4188_,
                    );
                if v___x_4189_ == 0 {
                    v___y_4216_ = v___x_4189_;
                    state = 10;
                    continue;
                } else {
                    v___x_4252_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_4253_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                            v_opts_4156_,
                            v___x_4252_,
                        );
                    if v___x_4253_ == 0 {
                        v___x_4254_ = l_Lean_trace_profiler_threshold;
                        v___x_4255_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_4156_, v___x_4254_);
                        v___x_4256_ = lean_float_of_nat(v___x_4255_);
                        v___x_4257_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__5);
                        v___x_4258_ = lean_float_div(v___x_4256_, v___x_4257_);
                        v___y_4247_ = v___x_4258_;
                        state = 15;
                        continue;
                    } else {
                        v___x_4259_ = l_Lean_trace_profiler_threshold;
                        v___x_4260_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__7(v_opts_4156_, v___x_4259_);
                        v___x_4261_ = lean_float_of_nat(v___x_4260_);
                        v___y_4247_ = v___x_4261_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_4193_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1_spec__2(v_fst_4164_);
                v___x_4194_ = l_Lean_TraceResult_toEmoji(v_result_4193_);
                v___x_4195_ = l_Lean_stringToMessageData(v___x_4194_);
                v___x_4196_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__1);
                if v_isShared_4187_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4186_, 7);
                    leanh::lean_ctor_set(v___x_4186_, 1, v___x_4196_);
                    leanh::lean_ctor_set(v___x_4186_, 0, v___x_4195_);
                    v___x_4198_ = v___x_4186_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 1, v___x_4196_);
                    v___x_4198_ = v_reuseFailAlloc_4209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4168_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4167_, 7);
                    leanh::lean_ctor_set(v___x_4167_, 1, v_a_4192_);
                    leanh::lean_ctor_set(v___x_4167_, 0, v___x_4198_);
                    v_m_4200_ = v___x_4167_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_a_4192_);
                    v_m_4200_ = v_reuseFailAlloc_4208_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4201_ = leanh::lean_box((v_result_4193_) as usize);
                v___x_4202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4202_, 0, v___x_4201_);
                v___x_4203_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__2);
                leanh::lean_inc_ref(v_tag_4155_);
                leanh::lean_inc_ref(v___x_4202_);
                leanh::lean_inc(v_cls_4153_);
                v_data_4204_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_4204_, 0, v_cls_4153_);
                leanh::lean_ctor_set(v_data_4204_, 1, v___x_4202_);
                leanh::lean_ctor_set(v_data_4204_, 2, v_tag_4155_);
                leanh::lean_ctor_set_float(
                    v_data_4204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4203_,
                );
                leanh::lean_ctor_set_float(
                    v_data_4204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4203_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_4204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_4154_,
                );
                if v___x_4189_ == 0 {
                    leanh::lean_dec_ref_known(v___x_4202_, 1);
                    leanh::lean_dec(v_snd_4184_);
                    leanh::lean_dec(v_fst_4183_);
                    leanh::lean_dec_ref(v_tag_4155_);
                    leanh::lean_dec(v_cls_4153_);
                    v___y_4170_ = v_m_4200_;
                    v___y_4171_ = v___y_4191_;
                    v_data_4172_ = v_data_4204_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_4204_, 3);
                    v_data_4205_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_4205_, 0, v_cls_4153_);
                    leanh::lean_ctor_set(v_data_4205_, 1, v___x_4202_);
                    leanh::lean_ctor_set(v_data_4205_, 2, v_tag_4155_);
                    v___x_4206_ = leanh::lean_unbox_float(v_fst_4183_);
                    leanh::lean_dec(v_fst_4183_);
                    leanh::lean_ctor_set_float(
                        v_data_4205_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_4206_,
                    );
                    v___x_4207_ = leanh::lean_unbox_float(v_snd_4184_);
                    leanh::lean_dec(v_snd_4184_);
                    leanh::lean_ctor_set_float(
                        v_data_4205_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_4207_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_4205_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_4154_,
                    );
                    v___y_4170_ = v_m_4200_;
                    v___y_4171_ = v___y_4191_;
                    v_data_4172_ = v_data_4205_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_4211_ = leanh::lean_ctor_get(v___y_4161_, 5);
                leanh::lean_inc(v___y_4162_);
                leanh::lean_inc_ref(v___y_4161_);
                leanh::lean_inc(v_fst_4164_);
                v___x_4212_ = leanh::lean_apply_4(
                    v_msg_4159_,
                    v_fst_4164_,
                    v___y_4161_,
                    v___y_4162_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_4212_) == 0 {
                    v_a_4213_ = leanh::lean_ctor_get(v___x_4212_, 0);
                    leanh::lean_inc(v_a_4213_);
                    leanh::lean_dec_ref_known(v___x_4212_, 1);
                    v___y_4191_ = v_ref_4211_;
                    v_a_4192_ = v_a_4213_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_4212_, 1);
                    v___x_4214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3___closed__4);
                    v___y_4191_ = v_ref_4211_;
                    v_a_4192_ = v___x_4214_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_4157_ == 0 {
                    if v___y_4216_ == 0 {
                        leanh::lean_del_object(v___x_4186_);
                        leanh::lean_dec(v_snd_4184_);
                        leanh::lean_dec(v_fst_4183_);
                        leanh::lean_del_object(v___x_4167_);
                        leanh::lean_dec_ref(v_msg_4159_);
                        leanh::lean_dec_ref(v_tag_4155_);
                        leanh::lean_dec(v_cls_4153_);
                        v___x_4217_ = lean_st_ref_take(v___y_4162_);
                        v_traceState_4218_ = leanh::lean_ctor_get(v___x_4217_, 4);
                        v_env_4219_ = leanh::lean_ctor_get(v___x_4217_, 0);
                        v_nextMacroScope_4220_ = leanh::lean_ctor_get(v___x_4217_, 1);
                        v_ngen_4221_ = leanh::lean_ctor_get(v___x_4217_, 2);
                        v_auxDeclNGen_4222_ = leanh::lean_ctor_get(v___x_4217_, 3);
                        v_cache_4223_ = leanh::lean_ctor_get(v___x_4217_, 5);
                        v_messages_4224_ = leanh::lean_ctor_get(v___x_4217_, 6);
                        v_infoState_4225_ = leanh::lean_ctor_get(v___x_4217_, 7);
                        v_snapshotTasks_4226_ = leanh::lean_ctor_get(v___x_4217_, 8);
                        v_isSharedCheck_4245_ =
                            (!leanh::lean_is_exclusive(v___x_4217_)) as u8;
                        if v_isSharedCheck_4245_ == 0 {
                            v___x_4228_ = v___x_4217_;
                            v_isShared_4229_ = v_isSharedCheck_4245_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_4226_);
                            leanh::lean_inc(v_infoState_4225_);
                            leanh::lean_inc(v_messages_4224_);
                            leanh::lean_inc(v_cache_4223_);
                            leanh::lean_inc(v_traceState_4218_);
                            leanh::lean_inc(v_auxDeclNGen_4222_);
                            leanh::lean_inc(v_ngen_4221_);
                            leanh::lean_inc(v_nextMacroScope_4220_);
                            leanh::lean_inc(v_env_4219_);
                            leanh::lean_dec(v___x_4217_);
                            v___x_4228_ = leanh::lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4245_;
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
                v_tid_4230_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4218_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4231_ = leanh::lean_ctor_get(v_traceState_4218_, 0);
                v_isSharedCheck_4244_ =
                    (!leanh::lean_is_exclusive(v_traceState_4218_)) as u8;
                if v_isSharedCheck_4244_ == 0 {
                    v___x_4233_ = v_traceState_4218_;
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4231_);
                    leanh::lean_dec(v_traceState_4218_);
                    v___x_4233_ = leanh::lean_box(0);
                    v_isShared_4234_ = v_isSharedCheck_4244_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4235_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_4158_, v_traces_4231_);
                leanh::lean_dec_ref(v_traces_4231_);
                if v_isShared_4234_ == 0 {
                    leanh::lean_ctor_set(v___x_4233_, 0, v___x_4235_);
                    v___x_4237_ = v___x_4233_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4235_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4243_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4230_,
                    );
                    v___x_4237_ = v_reuseFailAlloc_4243_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4229_ == 0 {
                    leanh::lean_ctor_set(v___x_4228_, 4, v___x_4237_);
                    v___x_4239_ = v___x_4228_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_env_4219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_nextMacroScope_4220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 2, v_ngen_4221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 3, v_auxDeclNGen_4222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 4, v___x_4237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 5, v_cache_4223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 6, v_messages_4224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 7, v_infoState_4225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 8, v_snapshotTasks_4226_);
                    v___x_4239_ = v_reuseFailAlloc_4242_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4240_ = lean_st_ref_set(v___y_4162_, v___x_4239_);
                v___x_4241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__3_spec__6___redArg(v_fst_4164_);
                return v___x_4241_;
            }
            15 => {
                v___x_4248_ = leanh::lean_unbox_float(v_snd_4184_);
                v___x_4249_ = leanh::lean_unbox_float(v_fst_4183_);
                v___x_4250_ = lean_float_sub(v___x_4248_, v___x_4249_);
                v___x_4251_ = lean_float_decLt(v___y_4247_, v___x_4250_);
                v___y_4216_ = v___x_4251_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1___boxed(
    mut v_cls_4264_: *mut leanh::LeanObject,
    mut v_collapsed_4265_: *mut leanh::LeanObject,
    mut v_tag_4266_: *mut leanh::LeanObject,
    mut v_opts_4267_: *mut leanh::LeanObject,
    mut v_clsEnabled_4268_: *mut leanh::LeanObject,
    mut v_oldTraces_4269_: *mut leanh::LeanObject,
    mut v_msg_4270_: *mut leanh::LeanObject,
    mut v_resStartStop_4271_: *mut leanh::LeanObject,
    mut v___y_4272_: *mut leanh::LeanObject,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_collapsed_boxed_4275_: u8 = 0;
    let mut v_clsEnabled_boxed_4276_: u8 = 0;
    let mut v_res_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4275_ = (leanh::lean_unbox(v_collapsed_4265_) as u8);
    v_clsEnabled_boxed_4276_ = (leanh::lean_unbox(v_clsEnabled_4268_) as u8);
    v_res_4277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v_cls_4264_, v_collapsed_boxed_4275_, v_tag_4266_, v_opts_4267_, v_clsEnabled_boxed_4276_, v_oldTraces_4269_, v_msg_4270_, v_resStartStop_4271_, v___y_4272_, v___y_4273_);
    leanh::lean_dec(v___y_4273_);
    leanh::lean_dec_ref(v___y_4272_);
    leanh::lean_dec_ref(v_opts_4267_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(
    mut v___f_4278_: *mut leanh::LeanObject,
    mut v_lratPath_4279_: *mut leanh::LeanObject,
    mut v_trimProofs_4280_: u8,
    mut v___f_4281_: *mut leanh::LeanObject,
    mut v_solver_4282_: *mut leanh::LeanObject,
    mut v_timeout_4283_: *mut leanh::LeanObject,
    mut v_binaryProofs_4284_: u8,
    mut v_solverMode_4285_: u8,
    mut v___f_4286_: *mut leanh::LeanObject,
    mut v___f_4287_: *mut leanh::LeanObject,
    mut v_cnfHandle_4288_: *mut leanh::LeanObject,
    mut v_cnfPath_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4298_: u8 = 0;
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_a_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_options_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4315_: u8 = 0;
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: u8 = 0;
    let mut v___y_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: f64 = 0.0;
    let mut v___x_4327_: f64 = 0.0;
    let mut v___x_4328_: f64 = 0.0;
    let mut v___x_4329_: f64 = 0.0;
    let mut v___x_4330_: f64 = 0.0;
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4340_: u8 = 0;
    let mut v_a_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: f64 = 0.0;
    let mut v___x_4344_: f64 = 0.0;
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4352_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4366_: u8 = 0;
    let mut v_a_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4370_: u8 = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_a_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4388_: u8 = 0;
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v___y_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v_assignment_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4409_: u8 = 0;
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4416_: u8 = 0;
    let mut v_a_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4420_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4424_: u8 = 0;
    let mut v___y_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4428_: u8 = 0;
    let mut v___y_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: f64 = 0.0;
    let mut v___x_4433_: f64 = 0.0;
    let mut v___x_4434_: f64 = 0.0;
    let mut v___x_4435_: f64 = 0.0;
    let mut v___x_4436_: f64 = 0.0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4446_: u8 = 0;
    let mut v_a_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: f64 = 0.0;
    let mut v___x_4450_: f64 = 0.0;
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: u8 = 0;
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v_a_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4476_: u8 = 0;
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4490_: u8 = 0;
    let mut v_a_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4498_: u8 = 0;
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_a_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4535_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4543_: u8 = 0;
    let mut v_a_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: u8 = 0;
    let mut v___y_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: f64 = 0.0;
    let mut v___x_4564_: f64 = 0.0;
    let mut v___x_4565_: f64 = 0.0;
    let mut v___x_4566_: f64 = 0.0;
    let mut v___x_4567_: f64 = 0.0;
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: f64 = 0.0;
    let mut v___x_4584_: f64 = 0.0;
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_a_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut v_a_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4627_: u8 = 0;
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v_a_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4654_: u8 = 0;
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4658_: u8 = 0;
    let mut v_a_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4662_: u8 = 0;
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4669_: u8 = 0;
    let mut v_a_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_a_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: u8 = 0;
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut v_a_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4721_: u8 = 0;
    let mut v_a_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4312_ = leanh::lean_ctor_get(v___y_4290_, 2);
                v_ref_4313_ = leanh::lean_ctor_get(v___y_4290_, 5);
                v_inheritedTraceOptions_4314_ = leanh::lean_ctor_get(v___y_4290_, 13);
                v_hasTrace_4315_ = leanh::lean_ctor_get_uint8(
                    v_options_4312_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_4316_ = l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__3;
                v___x_4317_ = 1;
                v___x_4318_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__0___closed__0;
                if v_hasTrace_4315_ == 0 {
                    leanh::lean_dec_ref(v___f_4287_);
                    v___x_4516_ = l_IO_lazyPure___redArg(v___f_4286_);
                    if leanh::lean_obj_tag(v___x_4516_) == 0 {
                        v_a_4517_ = leanh::lean_ctor_get(v___x_4516_, 0);
                        leanh::lean_inc(v_a_4517_);
                        leanh::lean_dec_ref_known(v___x_4516_, 1);
                        v___x_4518_ = lean_io_prim_handle_put_str(v_cnfHandle_4288_, v_a_4517_);
                        leanh::lean_dec(v_a_4517_);
                        if leanh::lean_obj_tag(v___x_4518_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4518_, 1);
                            v___x_4519_ = lean_io_prim_handle_flush(v_cnfHandle_4288_);
                            if leanh::lean_obj_tag(v___x_4519_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4519_, 1);
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_cnfPath_4289_);
                                leanh::lean_dec_ref(v_solver_4282_);
                                leanh::lean_dec_ref(v___f_4281_);
                                leanh::lean_dec_ref(v_lratPath_4279_);
                                leanh::lean_dec_ref(v___f_4278_);
                                v_a_4520_ = leanh::lean_ctor_get(v___x_4519_, 0);
                                v_isSharedCheck_4531_ =
                                    (!leanh::lean_is_exclusive(v___x_4519_)) as u8;
                                if v_isSharedCheck_4531_ == 0 {
                                    v___x_4522_ = v___x_4519_;
                                    v_isShared_4523_ = v_isSharedCheck_4531_;
                                    state = 39;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4520_);
                                    leanh::lean_dec(v___x_4519_);
                                    v___x_4522_ = leanh::lean_box(0);
                                    v_isShared_4523_ = v_isSharedCheck_4531_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_cnfPath_4289_);
                            leanh::lean_dec_ref(v_solver_4282_);
                            leanh::lean_dec_ref(v___f_4281_);
                            leanh::lean_dec_ref(v_lratPath_4279_);
                            leanh::lean_dec_ref(v___f_4278_);
                            v_a_4532_ = leanh::lean_ctor_get(v___x_4518_, 0);
                            v_isSharedCheck_4543_ =
                                (!leanh::lean_is_exclusive(v___x_4518_)) as u8;
                            if v_isSharedCheck_4543_ == 0 {
                                v___x_4534_ = v___x_4518_;
                                v_isShared_4535_ = v_isSharedCheck_4543_;
                                state = 41;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4532_);
                                leanh::lean_dec(v___x_4518_);
                                v___x_4534_ = leanh::lean_box(0);
                                v_isShared_4535_ = v_isSharedCheck_4543_;
                                state = 41;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_cnfPath_4289_);
                        leanh::lean_dec_ref(v_solver_4282_);
                        leanh::lean_dec_ref(v___f_4281_);
                        leanh::lean_dec_ref(v_lratPath_4279_);
                        leanh::lean_dec_ref(v___f_4278_);
                        v_a_4544_ = leanh::lean_ctor_get(v___x_4516_, 0);
                        v_isSharedCheck_4555_ =
                            (!leanh::lean_is_exclusive(v___x_4516_)) as u8;
                        if v_isSharedCheck_4555_ == 0 {
                            v___x_4546_ = v___x_4516_;
                            v_isShared_4547_ = v_isSharedCheck_4555_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4544_);
                            leanh::lean_dec(v___x_4516_);
                            v___x_4546_ = leanh::lean_box(0);
                            v_isShared_4547_ = v_isSharedCheck_4555_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    v___x_4556_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                    );
                    v___x_4557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4314_,
                        v_options_4312_,
                        v___x_4556_,
                    );
                    if v___x_4557_ == 0 {
                        v___x_4692_ = l_Lean_trace_profiler;
                        v___x_4693_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_4312_, v___x_4692_);
                        if v___x_4693_ == 0 {
                            leanh::lean_dec_ref(v___f_4287_);
                            v___x_4694_ = l_IO_lazyPure___redArg(v___f_4286_);
                            if leanh::lean_obj_tag(v___x_4694_) == 0 {
                                v_a_4695_ = leanh::lean_ctor_get(v___x_4694_, 0);
                                leanh::lean_inc(v_a_4695_);
                                leanh::lean_dec_ref_known(v___x_4694_, 1);
                                v___x_4696_ =
                                    lean_io_prim_handle_put_str(v_cnfHandle_4288_, v_a_4695_);
                                leanh::lean_dec(v_a_4695_);
                                if leanh::lean_obj_tag(v___x_4696_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4696_, 1);
                                    v___x_4697_ = lean_io_prim_handle_flush(v_cnfHandle_4288_);
                                    if leanh::lean_obj_tag(v___x_4697_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_4697_, 1);
                                        state = 35;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_cnfPath_4289_);
                                        leanh::lean_dec_ref(v_solver_4282_);
                                        leanh::lean_dec_ref(v___f_4281_);
                                        leanh::lean_dec_ref(v_lratPath_4279_);
                                        leanh::lean_dec_ref(v___f_4278_);
                                        v_a_4698_ = leanh::lean_ctor_get(v___x_4697_, 0);
                                        v_isSharedCheck_4709_ =
                                            (!leanh::lean_is_exclusive(v___x_4697_)) as u8;
                                        if v_isSharedCheck_4709_ == 0 {
                                            v___x_4700_ = v___x_4697_;
                                            v_isShared_4701_ = v_isSharedCheck_4709_;
                                            state = 66;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4698_);
                                            leanh::lean_dec(v___x_4697_);
                                            v___x_4700_ = leanh::lean_box(0);
                                            v_isShared_4701_ = v_isSharedCheck_4709_;
                                            state = 66;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_cnfPath_4289_);
                                    leanh::lean_dec_ref(v_solver_4282_);
                                    leanh::lean_dec_ref(v___f_4281_);
                                    leanh::lean_dec_ref(v_lratPath_4279_);
                                    leanh::lean_dec_ref(v___f_4278_);
                                    v_a_4710_ = leanh::lean_ctor_get(v___x_4696_, 0);
                                    v_isSharedCheck_4721_ =
                                        (!leanh::lean_is_exclusive(v___x_4696_)) as u8;
                                    if v_isSharedCheck_4721_ == 0 {
                                        v___x_4712_ = v___x_4696_;
                                        v_isShared_4713_ = v_isSharedCheck_4721_;
                                        state = 68;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4710_);
                                        leanh::lean_dec(v___x_4696_);
                                        v___x_4712_ = leanh::lean_box(0);
                                        v_isShared_4713_ = v_isSharedCheck_4721_;
                                        state = 68;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_cnfPath_4289_);
                                leanh::lean_dec_ref(v_solver_4282_);
                                leanh::lean_dec_ref(v___f_4281_);
                                leanh::lean_dec_ref(v_lratPath_4279_);
                                leanh::lean_dec_ref(v___f_4278_);
                                v_a_4722_ = leanh::lean_ctor_get(v___x_4694_, 0);
                                v_isSharedCheck_4733_ =
                                    (!leanh::lean_is_exclusive(v___x_4694_)) as u8;
                                if v_isSharedCheck_4733_ == 0 {
                                    v___x_4724_ = v___x_4694_;
                                    v_isShared_4725_ = v_isSharedCheck_4733_;
                                    state = 70;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4722_);
                                    leanh::lean_dec(v___x_4694_);
                                    v___x_4724_ = leanh::lean_box(0);
                                    v_isShared_4725_ = v_isSharedCheck_4733_;
                                    state = 70;
                                    continue;
                                }
                            }
                        } else {
                            state = 49;
                            continue;
                        }
                    } else {
                        state = 49;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4294_) == 0 {
                    v_a_4295_ = leanh::lean_ctor_get(v___y_4294_, 0);
                    v_isSharedCheck_4303_ = (!leanh::lean_is_exclusive(v___y_4294_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4297_ = v___y_4294_;
                        v_isShared_4298_ = v_isSharedCheck_4303_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4295_);
                        leanh::lean_dec(v___y_4294_);
                        v___x_4297_ = leanh::lean_box(0);
                        v_isShared_4298_ = v_isSharedCheck_4303_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4304_ = leanh::lean_ctor_get(v___y_4294_, 0);
                    v_isSharedCheck_4311_ = (!leanh::lean_is_exclusive(v___y_4294_)) as u8;
                    if v_isSharedCheck_4311_ == 0 {
                        v___x_4306_ = v___y_4294_;
                        v_isShared_4307_ = v_isSharedCheck_4311_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4304_);
                        leanh::lean_dec(v___y_4294_);
                        v___x_4306_ = leanh::lean_box(0);
                        v_isShared_4307_ = v_isSharedCheck_4311_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4299_, 0, v_a_4295_);
                if v_isShared_4298_ == 0 {
                    leanh::lean_ctor_set(v___x_4297_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4297_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4301_;
            }
            4 => {
                if v_isShared_4307_ == 0 {
                    v___x_4309_ = v___x_4306_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4309_;
            }
            6 => {
                v___x_4325_ = lean_io_mono_nanos_now();
                v___x_4326_ = lean_float_of_nat(v___y_4323_);
                v___x_4327_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9,
                );
                v___x_4328_ = lean_float_div(v___x_4326_, v___x_4327_);
                v___x_4329_ = lean_float_of_nat(v___x_4325_);
                v___x_4330_ = lean_float_div(v___x_4329_, v___x_4327_);
                v___x_4331_ = leanh::lean_box_float(v___x_4328_);
                v___x_4332_ = leanh::lean_box_float(v___x_4330_);
                v___x_4333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4333_, 0, v___x_4331_);
                leanh::lean_ctor_set(v___x_4333_, 1, v___x_4332_);
                v___x_4334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4334_, 0, v_a_4324_);
                leanh::lean_ctor_set(v___x_4334_, 1, v___x_4333_);
                v___x_4335_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_4316_, v___x_4317_, v___x_4318_, v___y_4320_, v___y_4322_, v___y_4321_, v___f_4278_, v___x_4334_, v___y_4290_, v___y_4291_);
                v___y_4294_ = v___x_4335_;
                state = 1;
                continue;
            }
            7 => {
                v___x_4342_ = lean_io_get_num_heartbeats();
                v___x_4343_ = lean_float_of_nat(v___y_4337_);
                v___x_4344_ = lean_float_of_nat(v___x_4342_);
                v___x_4345_ = leanh::lean_box_float(v___x_4343_);
                v___x_4346_ = leanh::lean_box_float(v___x_4344_);
                v___x_4347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4347_, 0, v___x_4345_);
                leanh::lean_ctor_set(v___x_4347_, 1, v___x_4346_);
                v___x_4348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4348_, 0, v_a_4341_);
                leanh::lean_ctor_set(v___x_4348_, 1, v___x_4347_);
                v___x_4349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__0(v___x_4316_, v___x_4317_, v___x_4318_, v___y_4338_, v___y_4340_, v___y_4339_, v___f_4278_, v___x_4348_, v___y_4290_, v___y_4291_);
                v___y_4294_ = v___x_4349_;
                state = 1;
                continue;
            }
            8 => {
                v___x_4353_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_4291_);
                v_a_4354_ = leanh::lean_ctor_get(v___x_4353_, 0);
                leanh::lean_inc(v_a_4354_);
                leanh::lean_dec_ref(v___x_4353_);
                v___x_4355_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_4356_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v___y_4351_,
                        v___x_4355_,
                    );
                if v___x_4356_ == 0 {
                    v___x_4357_ = lean_io_mono_nanos_now();
                    v___x_4358_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
                        v_lratPath_4279_,
                        v_trimProofs_4280_,
                        v___y_4290_,
                        v___y_4291_,
                    );
                    leanh::lean_dec_ref(v_lratPath_4279_);
                    if leanh::lean_obj_tag(v___x_4358_) == 0 {
                        v_a_4359_ = leanh::lean_ctor_get(v___x_4358_, 0);
                        v_isSharedCheck_4366_ =
                            (!leanh::lean_is_exclusive(v___x_4358_)) as u8;
                        if v_isSharedCheck_4366_ == 0 {
                            v___x_4361_ = v___x_4358_;
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4359_);
                            leanh::lean_dec(v___x_4358_);
                            v___x_4361_ = leanh::lean_box(0);
                            v_isShared_4362_ = v_isSharedCheck_4366_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_4367_ = leanh::lean_ctor_get(v___x_4358_, 0);
                        v_isSharedCheck_4374_ =
                            (!leanh::lean_is_exclusive(v___x_4358_)) as u8;
                        if v_isSharedCheck_4374_ == 0 {
                            v___x_4369_ = v___x_4358_;
                            v_isShared_4370_ = v_isSharedCheck_4374_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4367_);
                            leanh::lean_dec(v___x_4358_);
                            v___x_4369_ = leanh::lean_box(0);
                            v_isShared_4370_ = v_isSharedCheck_4374_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v___x_4375_ = lean_io_get_num_heartbeats();
                    v___x_4376_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
                        v_lratPath_4279_,
                        v_trimProofs_4280_,
                        v___y_4290_,
                        v___y_4291_,
                    );
                    leanh::lean_dec_ref(v_lratPath_4279_);
                    if leanh::lean_obj_tag(v___x_4376_) == 0 {
                        v_a_4377_ = leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4384_ =
                            (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4384_ == 0 {
                            v___x_4379_ = v___x_4376_;
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4377_);
                            leanh::lean_dec(v___x_4376_);
                            v___x_4379_ = leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4384_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_4385_ = leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4392_ =
                            (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4392_ == 0 {
                            v___x_4387_ = v___x_4376_;
                            v_isShared_4388_ = v_isSharedCheck_4392_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4385_);
                            leanh::lean_dec(v___x_4376_);
                            v___x_4387_ = leanh::lean_box(0);
                            v_isShared_4388_ = v_isSharedCheck_4392_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_4362_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4361_, 1);
                    v___x_4364_ = v___x_4361_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4365_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
                    v___x_4364_ = v_reuseFailAlloc_4365_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___y_4320_ = v___y_4351_;
                v___y_4321_ = v_a_4354_;
                v___y_4322_ = v___y_4352_;
                v___y_4323_ = v___x_4357_;
                v_a_4324_ = v___x_4364_;
                state = 6;
                continue;
            }
            11 => {
                if v_isShared_4370_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4369_, 0);
                    v___x_4372_ = v___x_4369_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
                    v___x_4372_ = v_reuseFailAlloc_4373_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___y_4320_ = v___y_4351_;
                v___y_4321_ = v_a_4354_;
                v___y_4322_ = v___y_4352_;
                v___y_4323_ = v___x_4357_;
                v_a_4324_ = v___x_4372_;
                state = 6;
                continue;
            }
            13 => {
                if v_isShared_4380_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4379_, 1);
                    v___x_4382_ = v___x_4379_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4337_ = v___x_4375_;
                v___y_4338_ = v___y_4351_;
                v___y_4339_ = v_a_4354_;
                v___y_4340_ = v___y_4352_;
                v_a_4341_ = v___x_4382_;
                state = 7;
                continue;
            }
            15 => {
                if v_isShared_4388_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4387_, 0);
                    v___x_4390_ = v___x_4387_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
                    v___x_4390_ = v_reuseFailAlloc_4391_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_4337_ = v___x_4375_;
                v___y_4338_ = v___y_4351_;
                v___y_4339_ = v_a_4354_;
                v___y_4340_ = v___y_4352_;
                v_a_4341_ = v___x_4390_;
                state = 7;
                continue;
            }
            17 => {
                if leanh::lean_obj_tag(v___y_4394_) == 0 {
                    v_a_4395_ = leanh::lean_ctor_get(v___y_4394_, 0);
                    v_isSharedCheck_4416_ = (!leanh::lean_is_exclusive(v___y_4394_)) as u8;
                    if v_isSharedCheck_4416_ == 0 {
                        v___x_4397_ = v___y_4394_;
                        v_isShared_4398_ = v_isSharedCheck_4416_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4395_);
                        leanh::lean_dec(v___y_4394_);
                        v___x_4397_ = leanh::lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4416_;
                        state = 18;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_lratPath_4279_);
                    leanh::lean_dec_ref(v___f_4278_);
                    v_a_4417_ = leanh::lean_ctor_get(v___y_4394_, 0);
                    v_isSharedCheck_4424_ = (!leanh::lean_is_exclusive(v___y_4394_)) as u8;
                    if v_isSharedCheck_4424_ == 0 {
                        v___x_4419_ = v___y_4394_;
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4417_);
                        leanh::lean_dec(v___y_4394_);
                        v___x_4419_ = leanh::lean_box(0);
                        v_isShared_4420_ = v_isSharedCheck_4424_;
                        state = 22;
                        continue;
                    }
                }
            }
            18 => {
                if leanh::lean_obj_tag(v_a_4395_) == 0 {
                    leanh::lean_dec_ref(v_lratPath_4279_);
                    leanh::lean_dec_ref(v___f_4278_);
                    v_assignment_4399_ = leanh::lean_ctor_get(v_a_4395_, 0);
                    v_isSharedCheck_4409_ = (!leanh::lean_is_exclusive(v_a_4395_)) as u8;
                    if v_isSharedCheck_4409_ == 0 {
                        v___x_4401_ = v_a_4395_;
                        v_isShared_4402_ = v_isSharedCheck_4409_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_assignment_4399_);
                        leanh::lean_dec(v_a_4395_);
                        v___x_4401_ = leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4409_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4397_);
                    leanh::lean_dec(v_a_4395_);
                    if v_hasTrace_4315_ == 0 {
                        leanh::lean_dec_ref(v___f_4278_);
                        v___x_4410_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
                            v_lratPath_4279_,
                            v_trimProofs_4280_,
                            v___y_4290_,
                            v___y_4291_,
                        );
                        leanh::lean_dec_ref(v_lratPath_4279_);
                        v___y_4294_ = v___x_4410_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4411_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                            ),
                            _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                        );
                        v___x_4412_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4314_,
                            v_options_4312_,
                            v___x_4411_,
                        );
                        if v___x_4412_ == 0 {
                            v___x_4413_ = l_Lean_trace_profiler;
                            v___x_4414_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_4312_, v___x_4413_);
                            if v___x_4414_ == 0 {
                                leanh::lean_dec_ref(v___f_4278_);
                                v___x_4415_ = l_Lean_Meta_Tactic_BVDecide_LratCert_ofFile(
                                    v_lratPath_4279_,
                                    v_trimProofs_4280_,
                                    v___y_4290_,
                                    v___y_4291_,
                                );
                                leanh::lean_dec_ref(v_lratPath_4279_);
                                v___y_4294_ = v___x_4415_;
                                state = 1;
                                continue;
                            } else {
                                v___y_4351_ = v_options_4312_;
                                v___y_4352_ = v___x_4412_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___y_4351_ = v_options_4312_;
                            v___y_4352_ = v___x_4412_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_assignment_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4408_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_4398_ == 0 {
                    leanh::lean_ctor_set(v___x_4397_, 0, v___x_4404_);
                    v___x_4406_ = v___x_4397_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4407_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
                    v___x_4406_ = v_reuseFailAlloc_4407_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4406_;
            }
            22 => {
                if v_isShared_4420_ == 0 {
                    v___x_4422_ = v___x_4419_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
                    v___x_4422_ = v_reuseFailAlloc_4423_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4422_;
            }
            24 => {
                v___x_4431_ = lean_io_mono_nanos_now();
                v___x_4432_ = lean_float_of_nat(v___y_4429_);
                v___x_4433_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9,
                );
                v___x_4434_ = lean_float_div(v___x_4432_, v___x_4433_);
                v___x_4435_ = lean_float_of_nat(v___x_4431_);
                v___x_4436_ = lean_float_div(v___x_4435_, v___x_4433_);
                v___x_4437_ = leanh::lean_box_float(v___x_4434_);
                v___x_4438_ = leanh::lean_box_float(v___x_4436_);
                v___x_4439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4439_, 0, v___x_4437_);
                leanh::lean_ctor_set(v___x_4439_, 1, v___x_4438_);
                v___x_4440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4440_, 0, v_a_4430_);
                leanh::lean_ctor_set(v___x_4440_, 1, v___x_4439_);
                v___x_4441_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_4316_, v___x_4317_, v___x_4318_, v___y_4426_, v___y_4428_, v___y_4427_, v___f_4281_, v___x_4440_, v___y_4290_, v___y_4291_);
                v___y_4394_ = v___x_4441_;
                state = 17;
                continue;
            }
            25 => {
                v___x_4448_ = lean_io_get_num_heartbeats();
                v___x_4449_ = lean_float_of_nat(v___y_4445_);
                v___x_4450_ = lean_float_of_nat(v___x_4448_);
                v___x_4451_ = leanh::lean_box_float(v___x_4449_);
                v___x_4452_ = leanh::lean_box_float(v___x_4450_);
                v___x_4453_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4453_, 0, v___x_4451_);
                leanh::lean_ctor_set(v___x_4453_, 1, v___x_4452_);
                v___x_4454_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4454_, 0, v_a_4447_);
                leanh::lean_ctor_set(v___x_4454_, 1, v___x_4453_);
                v___x_4455_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__1(v___x_4316_, v___x_4317_, v___x_4318_, v___y_4443_, v___y_4446_, v___y_4444_, v___f_4281_, v___x_4454_, v___y_4290_, v___y_4291_);
                v___y_4394_ = v___x_4455_;
                state = 17;
                continue;
            }
            26 => {
                v___x_4459_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_4291_);
                v_a_4460_ = leanh::lean_ctor_get(v___x_4459_, 0);
                leanh::lean_inc(v_a_4460_);
                leanh::lean_dec_ref(v___x_4459_);
                v___x_4461_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_4462_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v___y_4457_,
                        v___x_4461_,
                    );
                if v___x_4462_ == 0 {
                    v___x_4463_ = lean_io_mono_nanos_now();
                    leanh::lean_inc_ref(v_lratPath_4279_);
                    v___x_4464_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(
                        v_solver_4282_,
                        v_cnfPath_4289_,
                        v_lratPath_4279_,
                        v_timeout_4283_,
                        v_binaryProofs_4284_,
                        v_solverMode_4285_,
                        v___y_4290_,
                        v___y_4291_,
                    );
                    if leanh::lean_obj_tag(v___x_4464_) == 0 {
                        v_a_4465_ = leanh::lean_ctor_get(v___x_4464_, 0);
                        v_isSharedCheck_4472_ =
                            (!leanh::lean_is_exclusive(v___x_4464_)) as u8;
                        if v_isSharedCheck_4472_ == 0 {
                            v___x_4467_ = v___x_4464_;
                            v_isShared_4468_ = v_isSharedCheck_4472_;
                            state = 27;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4465_);
                            leanh::lean_dec(v___x_4464_);
                            v___x_4467_ = leanh::lean_box(0);
                            v_isShared_4468_ = v_isSharedCheck_4472_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v_a_4473_ = leanh::lean_ctor_get(v___x_4464_, 0);
                        v_isSharedCheck_4480_ =
                            (!leanh::lean_is_exclusive(v___x_4464_)) as u8;
                        if v_isSharedCheck_4480_ == 0 {
                            v___x_4475_ = v___x_4464_;
                            v_isShared_4476_ = v_isSharedCheck_4480_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4473_);
                            leanh::lean_dec(v___x_4464_);
                            v___x_4475_ = leanh::lean_box(0);
                            v_isShared_4476_ = v_isSharedCheck_4480_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    v___x_4481_ = lean_io_get_num_heartbeats();
                    leanh::lean_inc_ref(v_lratPath_4279_);
                    v___x_4482_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(
                        v_solver_4282_,
                        v_cnfPath_4289_,
                        v_lratPath_4279_,
                        v_timeout_4283_,
                        v_binaryProofs_4284_,
                        v_solverMode_4285_,
                        v___y_4290_,
                        v___y_4291_,
                    );
                    if leanh::lean_obj_tag(v___x_4482_) == 0 {
                        v_a_4483_ = leanh::lean_ctor_get(v___x_4482_, 0);
                        v_isSharedCheck_4490_ =
                            (!leanh::lean_is_exclusive(v___x_4482_)) as u8;
                        if v_isSharedCheck_4490_ == 0 {
                            v___x_4485_ = v___x_4482_;
                            v_isShared_4486_ = v_isSharedCheck_4490_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4483_);
                            leanh::lean_dec(v___x_4482_);
                            v___x_4485_ = leanh::lean_box(0);
                            v_isShared_4486_ = v_isSharedCheck_4490_;
                            state = 31;
                            continue;
                        }
                    } else {
                        v_a_4491_ = leanh::lean_ctor_get(v___x_4482_, 0);
                        v_isSharedCheck_4498_ =
                            (!leanh::lean_is_exclusive(v___x_4482_)) as u8;
                        if v_isSharedCheck_4498_ == 0 {
                            v___x_4493_ = v___x_4482_;
                            v_isShared_4494_ = v_isSharedCheck_4498_;
                            state = 33;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4491_);
                            leanh::lean_dec(v___x_4482_);
                            v___x_4493_ = leanh::lean_box(0);
                            v_isShared_4494_ = v_isSharedCheck_4498_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            27 => {
                if v_isShared_4468_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4467_, 1);
                    v___x_4470_ = v___x_4467_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___y_4426_ = v___y_4457_;
                v___y_4427_ = v_a_4460_;
                v___y_4428_ = v___y_4458_;
                v___y_4429_ = v___x_4463_;
                v_a_4430_ = v___x_4470_;
                state = 24;
                continue;
            }
            29 => {
                if v_isShared_4476_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4475_, 0);
                    v___x_4478_ = v___x_4475_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4479_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
                    v___x_4478_ = v_reuseFailAlloc_4479_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___y_4426_ = v___y_4457_;
                v___y_4427_ = v_a_4460_;
                v___y_4428_ = v___y_4458_;
                v___y_4429_ = v___x_4463_;
                v_a_4430_ = v___x_4478_;
                state = 24;
                continue;
            }
            31 => {
                if v_isShared_4486_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4485_, 1);
                    v___x_4488_ = v___x_4485_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
                    v___x_4488_ = v_reuseFailAlloc_4489_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___y_4443_ = v___y_4457_;
                v___y_4444_ = v_a_4460_;
                v___y_4445_ = v___x_4481_;
                v___y_4446_ = v___y_4458_;
                v_a_4447_ = v___x_4488_;
                state = 25;
                continue;
            }
            33 => {
                if v_isShared_4494_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4493_, 0);
                    v___x_4496_ = v___x_4493_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4497_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4497_, 0, v_a_4491_);
                    v___x_4496_ = v_reuseFailAlloc_4497_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___y_4443_ = v___y_4457_;
                v___y_4444_ = v_a_4460_;
                v___y_4445_ = v___x_4481_;
                v___y_4446_ = v___y_4458_;
                v_a_4447_ = v___x_4496_;
                state = 25;
                continue;
            }
            35 => {
                if v_hasTrace_4315_ == 0 {
                    leanh::lean_dec_ref(v___f_4281_);
                    leanh::lean_inc_ref(v_lratPath_4279_);
                    v___x_4500_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(
                        v_solver_4282_,
                        v_cnfPath_4289_,
                        v_lratPath_4279_,
                        v_timeout_4283_,
                        v_binaryProofs_4284_,
                        v_solverMode_4285_,
                        v___y_4290_,
                        v___y_4291_,
                    );
                    v___y_4394_ = v___x_4500_;
                    state = 17;
                    continue;
                } else {
                    v___x_4501_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__6,
                    );
                    v___x_4502_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4314_,
                        v_options_4312_,
                        v___x_4501_,
                    );
                    if v___x_4502_ == 0 {
                        v___x_4503_ = l_Lean_trace_profiler;
                        v___x_4504_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(v_options_4312_, v___x_4503_);
                        if v___x_4504_ == 0 {
                            leanh::lean_dec_ref(v___f_4281_);
                            leanh::lean_inc_ref(v_lratPath_4279_);
                            v___x_4505_ = l_Lean_Meta_Tactic_BVDecide_External_satQuery(
                                v_solver_4282_,
                                v_cnfPath_4289_,
                                v_lratPath_4279_,
                                v_timeout_4283_,
                                v_binaryProofs_4284_,
                                v_solverMode_4285_,
                                v___y_4290_,
                                v___y_4291_,
                            );
                            v___y_4394_ = v___x_4505_;
                            state = 17;
                            continue;
                        } else {
                            v___y_4457_ = v_options_4312_;
                            v___y_4458_ = v___x_4502_;
                            state = 26;
                            continue;
                        }
                    } else {
                        v___y_4457_ = v_options_4312_;
                        v___y_4458_ = v___x_4502_;
                        state = 26;
                        continue;
                    }
                }
            }
            36 => {
                if leanh::lean_obj_tag(v___y_4507_) == 0 {
                    leanh::lean_dec_ref_known(v___y_4507_, 1);
                    state = 35;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_cnfPath_4289_);
                    leanh::lean_dec_ref(v_solver_4282_);
                    leanh::lean_dec_ref(v___f_4281_);
                    leanh::lean_dec_ref(v_lratPath_4279_);
                    leanh::lean_dec_ref(v___f_4278_);
                    v_a_4508_ = leanh::lean_ctor_get(v___y_4507_, 0);
                    v_isSharedCheck_4515_ = (!leanh::lean_is_exclusive(v___y_4507_)) as u8;
                    if v_isSharedCheck_4515_ == 0 {
                        v___x_4510_ = v___y_4507_;
                        v_isShared_4511_ = v_isSharedCheck_4515_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4508_);
                        leanh::lean_dec(v___y_4507_);
                        v___x_4510_ = leanh::lean_box(0);
                        v_isShared_4511_ = v_isSharedCheck_4515_;
                        state = 37;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_4511_ == 0 {
                    v___x_4513_ = v___x_4510_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
                    v___x_4513_ = v_reuseFailAlloc_4514_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4513_;
            }
            39 => {
                v___x_4524_ = lean_io_error_to_string(v_a_4520_);
                v___x_4525_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4525_, 0, v___x_4524_);
                v___x_4526_ = l_Lean_MessageData_ofFormat(v___x_4525_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4527_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4527_, 1, v___x_4526_);
                if v_isShared_4523_ == 0 {
                    leanh::lean_ctor_set(v___x_4522_, 0, v___x_4527_);
                    v___x_4529_ = v___x_4522_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v___x_4527_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4529_;
            }
            41 => {
                v___x_4536_ = lean_io_error_to_string(v_a_4532_);
                v___x_4537_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4537_, 0, v___x_4536_);
                v___x_4538_ = l_Lean_MessageData_ofFormat(v___x_4537_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4539_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4539_, 1, v___x_4538_);
                if v_isShared_4535_ == 0 {
                    leanh::lean_ctor_set(v___x_4534_, 0, v___x_4539_);
                    v___x_4541_ = v___x_4534_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4539_);
                    v___x_4541_ = v_reuseFailAlloc_4542_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4541_;
            }
            43 => {
                v___x_4548_ = lean_io_error_to_string(v_a_4544_);
                v___x_4549_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4549_, 0, v___x_4548_);
                v___x_4550_ = l_Lean_MessageData_ofFormat(v___x_4549_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4551_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4551_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4551_, 1, v___x_4550_);
                if v_isShared_4547_ == 0 {
                    leanh::lean_ctor_set(v___x_4546_, 0, v___x_4551_);
                    v___x_4553_ = v___x_4546_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
                    v___x_4553_ = v_reuseFailAlloc_4554_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4553_;
            }
            45 => {
                v___x_4562_ = lean_io_mono_nanos_now();
                v___x_4563_ = lean_float_of_nat(v___y_4560_);
                v___x_4564_ = leanh::lean_float_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_LratCert_load___closed__9,
                );
                v___x_4565_ = lean_float_div(v___x_4563_, v___x_4564_);
                v___x_4566_ = lean_float_of_nat(v___x_4562_);
                v___x_4567_ = lean_float_div(v___x_4566_, v___x_4564_);
                v___x_4568_ = leanh::lean_box_float(v___x_4565_);
                v___x_4569_ = leanh::lean_box_float(v___x_4567_);
                v___x_4570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4570_, 0, v___x_4568_);
                leanh::lean_ctor_set(v___x_4570_, 1, v___x_4569_);
                v___x_4571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4571_, 0, v_a_4561_);
                leanh::lean_ctor_set(v___x_4571_, 1, v___x_4570_);
                v___x_4572_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_4316_, v___x_4317_, v___x_4318_, v_options_4312_, v___x_4557_, v___y_4559_, v___f_4287_, v___x_4571_, v___y_4290_, v___y_4291_);
                v___y_4507_ = v___x_4572_;
                state = 36;
                continue;
            }
            46 => {
                v___x_4577_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4577_, 0, v_a_4576_);
                v___y_4559_ = v___y_4574_;
                v___y_4560_ = v___y_4575_;
                v_a_4561_ = v___x_4577_;
                state = 45;
                continue;
            }
            47 => {
                v___x_4582_ = lean_io_get_num_heartbeats();
                v___x_4583_ = lean_float_of_nat(v___y_4580_);
                v___x_4584_ = lean_float_of_nat(v___x_4582_);
                v___x_4585_ = leanh::lean_box_float(v___x_4583_);
                v___x_4586_ = leanh::lean_box_float(v___x_4584_);
                v___x_4587_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4587_, 0, v___x_4585_);
                leanh::lean_ctor_set(v___x_4587_, 1, v___x_4586_);
                v___x_4588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4588_, 0, v_a_4581_);
                leanh::lean_ctor_set(v___x_4588_, 1, v___x_4587_);
                v___x_4589_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__2(v___x_4316_, v___x_4317_, v___x_4318_, v_options_4312_, v___x_4557_, v___y_4579_, v___f_4287_, v___x_4588_, v___y_4290_, v___y_4291_);
                v___y_4507_ = v___x_4589_;
                state = 36;
                continue;
            }
            48 => {
                v___x_4594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4594_, 0, v_a_4593_);
                v___y_4579_ = v___y_4591_;
                v___y_4580_ = v___y_4592_;
                v_a_4581_ = v___x_4594_;
                state = 47;
                continue;
            }
            49 => {
                v___x_4596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__1___redArg(v___y_4291_);
                v_a_4597_ = leanh::lean_ctor_get(v___x_4596_, 0);
                leanh::lean_inc(v_a_4597_);
                leanh::lean_dec_ref(v___x_4596_);
                v___x_4598_ = l_Lean_trace_profiler_useHeartbeats;
                v___x_4599_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_LratCert_load_spec__2(
                        v_options_4312_,
                        v___x_4598_,
                    );
                if v___x_4599_ == 0 {
                    v___x_4600_ = lean_io_mono_nanos_now();
                    v___x_4601_ = l_IO_lazyPure___redArg(v___f_4286_);
                    if leanh::lean_obj_tag(v___x_4601_) == 0 {
                        v_a_4602_ = leanh::lean_ctor_get(v___x_4601_, 0);
                        leanh::lean_inc(v_a_4602_);
                        leanh::lean_dec_ref_known(v___x_4601_, 1);
                        v___x_4603_ = lean_io_prim_handle_put_str(v_cnfHandle_4288_, v_a_4602_);
                        leanh::lean_dec(v_a_4602_);
                        if leanh::lean_obj_tag(v___x_4603_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4603_, 1);
                            v___x_4604_ = lean_io_prim_handle_flush(v_cnfHandle_4288_);
                            if leanh::lean_obj_tag(v___x_4604_) == 0 {
                                v_a_4605_ = leanh::lean_ctor_get(v___x_4604_, 0);
                                v_isSharedCheck_4612_ =
                                    (!leanh::lean_is_exclusive(v___x_4604_)) as u8;
                                if v_isSharedCheck_4612_ == 0 {
                                    v___x_4607_ = v___x_4604_;
                                    v_isShared_4608_ = v_isSharedCheck_4612_;
                                    state = 50;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4605_);
                                    leanh::lean_dec(v___x_4604_);
                                    v___x_4607_ = leanh::lean_box(0);
                                    v_isShared_4608_ = v_isSharedCheck_4612_;
                                    state = 50;
                                    continue;
                                }
                            } else {
                                v_a_4613_ = leanh::lean_ctor_get(v___x_4604_, 0);
                                v_isSharedCheck_4623_ =
                                    (!leanh::lean_is_exclusive(v___x_4604_)) as u8;
                                if v_isSharedCheck_4623_ == 0 {
                                    v___x_4615_ = v___x_4604_;
                                    v_isShared_4616_ = v_isSharedCheck_4623_;
                                    state = 52;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4613_);
                                    leanh::lean_dec(v___x_4604_);
                                    v___x_4615_ = leanh::lean_box(0);
                                    v_isShared_4616_ = v_isSharedCheck_4623_;
                                    state = 52;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4624_ = leanh::lean_ctor_get(v___x_4603_, 0);
                            v_isSharedCheck_4634_ =
                                (!leanh::lean_is_exclusive(v___x_4603_)) as u8;
                            if v_isSharedCheck_4634_ == 0 {
                                v___x_4626_ = v___x_4603_;
                                v_isShared_4627_ = v_isSharedCheck_4634_;
                                state = 54;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4624_);
                                leanh::lean_dec(v___x_4603_);
                                v___x_4626_ = leanh::lean_box(0);
                                v_isShared_4627_ = v_isSharedCheck_4634_;
                                state = 54;
                                continue;
                            }
                        }
                    } else {
                        v_a_4635_ = leanh::lean_ctor_get(v___x_4601_, 0);
                        v_isSharedCheck_4645_ =
                            (!leanh::lean_is_exclusive(v___x_4601_)) as u8;
                        if v_isSharedCheck_4645_ == 0 {
                            v___x_4637_ = v___x_4601_;
                            v_isShared_4638_ = v_isSharedCheck_4645_;
                            state = 56;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4635_);
                            leanh::lean_dec(v___x_4601_);
                            v___x_4637_ = leanh::lean_box(0);
                            v_isShared_4638_ = v_isSharedCheck_4645_;
                            state = 56;
                            continue;
                        }
                    }
                } else {
                    v___x_4646_ = lean_io_get_num_heartbeats();
                    v___x_4647_ = l_IO_lazyPure___redArg(v___f_4286_);
                    if leanh::lean_obj_tag(v___x_4647_) == 0 {
                        v_a_4648_ = leanh::lean_ctor_get(v___x_4647_, 0);
                        leanh::lean_inc(v_a_4648_);
                        leanh::lean_dec_ref_known(v___x_4647_, 1);
                        v___x_4649_ = lean_io_prim_handle_put_str(v_cnfHandle_4288_, v_a_4648_);
                        leanh::lean_dec(v_a_4648_);
                        if leanh::lean_obj_tag(v___x_4649_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4649_, 1);
                            v___x_4650_ = lean_io_prim_handle_flush(v_cnfHandle_4288_);
                            if leanh::lean_obj_tag(v___x_4650_) == 0 {
                                v_a_4651_ = leanh::lean_ctor_get(v___x_4650_, 0);
                                v_isSharedCheck_4658_ =
                                    (!leanh::lean_is_exclusive(v___x_4650_)) as u8;
                                if v_isSharedCheck_4658_ == 0 {
                                    v___x_4653_ = v___x_4650_;
                                    v_isShared_4654_ = v_isSharedCheck_4658_;
                                    state = 58;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4651_);
                                    leanh::lean_dec(v___x_4650_);
                                    v___x_4653_ = leanh::lean_box(0);
                                    v_isShared_4654_ = v_isSharedCheck_4658_;
                                    state = 58;
                                    continue;
                                }
                            } else {
                                v_a_4659_ = leanh::lean_ctor_get(v___x_4650_, 0);
                                v_isSharedCheck_4669_ =
                                    (!leanh::lean_is_exclusive(v___x_4650_)) as u8;
                                if v_isSharedCheck_4669_ == 0 {
                                    v___x_4661_ = v___x_4650_;
                                    v_isShared_4662_ = v_isSharedCheck_4669_;
                                    state = 60;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4659_);
                                    leanh::lean_dec(v___x_4650_);
                                    v___x_4661_ = leanh::lean_box(0);
                                    v_isShared_4662_ = v_isSharedCheck_4669_;
                                    state = 60;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4670_ = leanh::lean_ctor_get(v___x_4649_, 0);
                            v_isSharedCheck_4680_ =
                                (!leanh::lean_is_exclusive(v___x_4649_)) as u8;
                            if v_isSharedCheck_4680_ == 0 {
                                v___x_4672_ = v___x_4649_;
                                v_isShared_4673_ = v_isSharedCheck_4680_;
                                state = 62;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4670_);
                                leanh::lean_dec(v___x_4649_);
                                v___x_4672_ = leanh::lean_box(0);
                                v_isShared_4673_ = v_isSharedCheck_4680_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        v_a_4681_ = leanh::lean_ctor_get(v___x_4647_, 0);
                        v_isSharedCheck_4691_ =
                            (!leanh::lean_is_exclusive(v___x_4647_)) as u8;
                        if v_isSharedCheck_4691_ == 0 {
                            v___x_4683_ = v___x_4647_;
                            v_isShared_4684_ = v_isSharedCheck_4691_;
                            state = 64;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4681_);
                            leanh::lean_dec(v___x_4647_);
                            v___x_4683_ = leanh::lean_box(0);
                            v_isShared_4684_ = v_isSharedCheck_4691_;
                            state = 64;
                            continue;
                        }
                    }
                }
            }
            50 => {
                if v_isShared_4608_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4607_, 1);
                    v___x_4610_ = v___x_4607_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___y_4559_ = v_a_4597_;
                v___y_4560_ = v___x_4600_;
                v_a_4561_ = v___x_4610_;
                state = 45;
                continue;
            }
            52 => {
                v___x_4617_ = lean_io_error_to_string(v_a_4613_);
                if v_isShared_4616_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4615_, 3);
                    leanh::lean_ctor_set(v___x_4615_, 0, v___x_4617_);
                    v___x_4619_ = v___x_4615_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4622_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4617_);
                    v___x_4619_ = v_reuseFailAlloc_4622_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___x_4620_ = l_Lean_MessageData_ofFormat(v___x_4619_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4621_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4621_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4621_, 1, v___x_4620_);
                v___y_4574_ = v_a_4597_;
                v___y_4575_ = v___x_4600_;
                v_a_4576_ = v___x_4621_;
                state = 46;
                continue;
            }
            54 => {
                v___x_4628_ = lean_io_error_to_string(v_a_4624_);
                if v_isShared_4627_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4626_, 3);
                    leanh::lean_ctor_set(v___x_4626_, 0, v___x_4628_);
                    v___x_4630_ = v___x_4626_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_4633_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4633_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                v___x_4631_ = l_Lean_MessageData_ofFormat(v___x_4630_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4632_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4632_, 1, v___x_4631_);
                v___y_4574_ = v_a_4597_;
                v___y_4575_ = v___x_4600_;
                v_a_4576_ = v___x_4632_;
                state = 46;
                continue;
            }
            56 => {
                v___x_4639_ = lean_io_error_to_string(v_a_4635_);
                if v_isShared_4638_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4637_, 3);
                    leanh::lean_ctor_set(v___x_4637_, 0, v___x_4639_);
                    v___x_4641_ = v___x_4637_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4639_);
                    v___x_4641_ = v_reuseFailAlloc_4644_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                v___x_4642_ = l_Lean_MessageData_ofFormat(v___x_4641_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4643_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4643_, 1, v___x_4642_);
                v___y_4574_ = v_a_4597_;
                v___y_4575_ = v___x_4600_;
                v_a_4576_ = v___x_4643_;
                state = 46;
                continue;
            }
            58 => {
                if v_isShared_4654_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4653_, 1);
                    v___x_4656_ = v___x_4653_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_4657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
                    v___x_4656_ = v_reuseFailAlloc_4657_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                v___y_4579_ = v_a_4597_;
                v___y_4580_ = v___x_4646_;
                v_a_4581_ = v___x_4656_;
                state = 47;
                continue;
            }
            60 => {
                v___x_4663_ = lean_io_error_to_string(v_a_4659_);
                if v_isShared_4662_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4661_, 3);
                    leanh::lean_ctor_set(v___x_4661_, 0, v___x_4663_);
                    v___x_4665_ = v___x_4661_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4668_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4663_);
                    v___x_4665_ = v_reuseFailAlloc_4668_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                v___x_4666_ = l_Lean_MessageData_ofFormat(v___x_4665_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4667_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4667_, 1, v___x_4666_);
                v___y_4591_ = v_a_4597_;
                v___y_4592_ = v___x_4646_;
                v_a_4593_ = v___x_4667_;
                state = 48;
                continue;
            }
            62 => {
                v___x_4674_ = lean_io_error_to_string(v_a_4670_);
                if v_isShared_4673_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4672_, 3);
                    leanh::lean_ctor_set(v___x_4672_, 0, v___x_4674_);
                    v___x_4676_ = v___x_4672_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4674_);
                    v___x_4676_ = v_reuseFailAlloc_4679_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                v___x_4677_ = l_Lean_MessageData_ofFormat(v___x_4676_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4678_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4678_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4678_, 1, v___x_4677_);
                v___y_4591_ = v_a_4597_;
                v___y_4592_ = v___x_4646_;
                v_a_4593_ = v___x_4678_;
                state = 48;
                continue;
            }
            64 => {
                v___x_4685_ = lean_io_error_to_string(v_a_4681_);
                if v_isShared_4684_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4683_, 3);
                    leanh::lean_ctor_set(v___x_4683_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4683_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_4690_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4685_);
                    v___x_4687_ = v_reuseFailAlloc_4690_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                v___x_4688_ = l_Lean_MessageData_ofFormat(v___x_4687_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4689_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4689_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4689_, 1, v___x_4688_);
                v___y_4591_ = v_a_4597_;
                v___y_4592_ = v___x_4646_;
                v_a_4593_ = v___x_4689_;
                state = 48;
                continue;
            }
            66 => {
                v___x_4702_ = lean_io_error_to_string(v_a_4698_);
                v___x_4703_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4703_, 0, v___x_4702_);
                v___x_4704_ = l_Lean_MessageData_ofFormat(v___x_4703_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4705_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4705_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4705_, 1, v___x_4704_);
                if v_isShared_4701_ == 0 {
                    leanh::lean_ctor_set(v___x_4700_, 0, v___x_4705_);
                    v___x_4707_ = v___x_4700_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
                    v___x_4707_ = v_reuseFailAlloc_4708_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4707_;
            }
            68 => {
                v___x_4714_ = lean_io_error_to_string(v_a_4710_);
                v___x_4715_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4715_, 0, v___x_4714_);
                v___x_4716_ = l_Lean_MessageData_ofFormat(v___x_4715_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4717_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4717_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4717_, 1, v___x_4716_);
                if v_isShared_4713_ == 0 {
                    leanh::lean_ctor_set(v___x_4712_, 0, v___x_4717_);
                    v___x_4719_ = v___x_4712_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_4720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4717_);
                    v___x_4719_ = v_reuseFailAlloc_4720_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_4719_;
            }
            70 => {
                v___x_4726_ = lean_io_error_to_string(v_a_4722_);
                v___x_4727_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4727_, 0, v___x_4726_);
                v___x_4728_ = l_Lean_MessageData_ofFormat(v___x_4727_);
                leanh::lean_inc(v_ref_4313_);
                v___x_4729_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4729_, 0, v_ref_4313_);
                leanh::lean_ctor_set(v___x_4729_, 1, v___x_4728_);
                if v_isShared_4725_ == 0 {
                    leanh::lean_ctor_set(v___x_4724_, 0, v___x_4729_);
                    v___x_4731_ = v___x_4724_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_4732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4729_);
                    v___x_4731_ = v_reuseFailAlloc_4732_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_4731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed(
    mut v___f_4734_: *mut leanh::LeanObject,
    mut v_lratPath_4735_: *mut leanh::LeanObject,
    mut v_trimProofs_4736_: *mut leanh::LeanObject,
    mut v___f_4737_: *mut leanh::LeanObject,
    mut v_solver_4738_: *mut leanh::LeanObject,
    mut v_timeout_4739_: *mut leanh::LeanObject,
    mut v_binaryProofs_4740_: *mut leanh::LeanObject,
    mut v_solverMode_4741_: *mut leanh::LeanObject,
    mut v___f_4742_: *mut leanh::LeanObject,
    mut v___f_4743_: *mut leanh::LeanObject,
    mut v_cnfHandle_4744_: *mut leanh::LeanObject,
    mut v_cnfPath_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trimProofs_boxed_4749_: u8 = 0;
    let mut v_binaryProofs_boxed_4750_: u8 = 0;
    let mut v_solverMode_boxed_4751_: u8 = 0;
    let mut v_res_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trimProofs_boxed_4749_ = (leanh::lean_unbox(v_trimProofs_4736_) as u8);
    v_binaryProofs_boxed_4750_ = (leanh::lean_unbox(v_binaryProofs_4740_) as u8);
    v_solverMode_boxed_4751_ = (leanh::lean_unbox(v_solverMode_4741_) as u8);
    v_res_4752_ = l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4(
        v___f_4734_,
        v_lratPath_4735_,
        v_trimProofs_boxed_4749_,
        v___f_4737_,
        v_solver_4738_,
        v_timeout_4739_,
        v_binaryProofs_boxed_4750_,
        v_solverMode_boxed_4751_,
        v___f_4742_,
        v___f_4743_,
        v_cnfHandle_4744_,
        v_cnfPath_4745_,
        v___y_4746_,
        v___y_4747_,
    );
    leanh::lean_dec(v___y_4747_);
    leanh::lean_dec_ref(v___y_4746_);
    leanh::lean_dec(v_cnfHandle_4744_);
    leanh::lean_dec(v_timeout_4739_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal(
    mut v_cnf_4756_: *mut leanh::LeanObject,
    mut v_solver_4757_: *mut leanh::LeanObject,
    mut v_lratPath_4758_: *mut leanh::LeanObject,
    mut v_trimProofs_4759_: u8,
    mut v_timeout_4760_: *mut leanh::LeanObject,
    mut v_binaryProofs_4761_: u8,
    mut v_solverMode_4762_: u8,
    mut v_a_4763_: *mut leanh::LeanObject,
    mut v_a_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4766_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_runExternal___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4766_, 0, v_cnf_4756_);
    v___f_4767_ = l_Lean_Meta_Tactic_BVDecide_runExternal___closed__0;
    v___f_4768_ = l_Lean_Meta_Tactic_BVDecide_runExternal___closed__1;
    v___f_4769_ = l_Lean_Meta_Tactic_BVDecide_runExternal___closed__2;
    v___x_4770_ = leanh::lean_box((v_trimProofs_4759_) as usize);
    v___x_4771_ = leanh::lean_box((v_binaryProofs_4761_) as usize);
    v___x_4772_ = leanh::lean_box((v_solverMode_4762_) as usize);
    v___f_4773_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_runExternal___lam__4___boxed as *mut core::ffi::c_void,
        15,
        10,
    );
    leanh::lean_closure_set(v___f_4773_, 0, v___f_4768_);
    leanh::lean_closure_set(v___f_4773_, 1, v_lratPath_4758_);
    leanh::lean_closure_set(v___f_4773_, 2, v___x_4770_);
    leanh::lean_closure_set(v___f_4773_, 3, v___f_4767_);
    leanh::lean_closure_set(v___f_4773_, 4, v_solver_4757_);
    leanh::lean_closure_set(v___f_4773_, 5, v_timeout_4760_);
    leanh::lean_closure_set(v___f_4773_, 6, v___x_4771_);
    leanh::lean_closure_set(v___f_4773_, 7, v___x_4772_);
    leanh::lean_closure_set(v___f_4773_, 8, v___f_4766_);
    leanh::lean_closure_set(v___f_4773_, 9, v___f_4769_);
    v___x_4774_ =
        l_IO_FS_withTempFile___at___00Lean_Meta_Tactic_BVDecide_runExternal_spec__3___redArg(
            v___f_4773_,
            v_a_4763_,
            v_a_4764_,
        );
    return v___x_4774_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_runExternal___boxed(
    mut v_cnf_4775_: *mut leanh::LeanObject,
    mut v_solver_4776_: *mut leanh::LeanObject,
    mut v_lratPath_4777_: *mut leanh::LeanObject,
    mut v_trimProofs_4778_: *mut leanh::LeanObject,
    mut v_timeout_4779_: *mut leanh::LeanObject,
    mut v_binaryProofs_4780_: *mut leanh::LeanObject,
    mut v_solverMode_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
    mut v_a_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_trimProofs_boxed_4785_: u8 = 0;
    let mut v_binaryProofs_boxed_4786_: u8 = 0;
    let mut v_solverMode_boxed_4787_: u8 = 0;
    let mut v_res_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_trimProofs_boxed_4785_ = (leanh::lean_unbox(v_trimProofs_4778_) as u8);
    v_binaryProofs_boxed_4786_ = (leanh::lean_unbox(v_binaryProofs_4780_) as u8);
    v_solverMode_boxed_4787_ = (leanh::lean_unbox(v_solverMode_4781_) as u8);
    v_res_4788_ = l_Lean_Meta_Tactic_BVDecide_runExternal(
        v_cnf_4775_,
        v_solver_4776_,
        v_lratPath_4777_,
        v_trimProofs_boxed_4785_,
        v_timeout_4779_,
        v_binaryProofs_boxed_4786_,
        v_solverMode_boxed_4787_,
        v_a_4782_,
        v_a_4783_,
    );
    leanh::lean_dec(v_a_4783_);
    leanh::lean_dec_ref(v_a_4782_);
    return v_res_4788_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction = _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction();
    leanh::lean_mark_persistent(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Cert_0__Lean_Meta_Tactic_BVDecide_instToExprIntAction);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_External(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_LRAT_Cert(builtin);
}