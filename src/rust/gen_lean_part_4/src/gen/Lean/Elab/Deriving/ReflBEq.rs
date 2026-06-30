// Lean compiler output
// Module: Lean.Elab.Deriving.ReflBEq
// Imports: Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util Init.LawfulBEqTactics
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_mkCIdent;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node6, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_List_lengthTR___redArg, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_isNested;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, l_Lean_Elab_registerDerivingHandler,
    runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Deriving::Util::{
    initialize_Lean_Elab_Deriving_Util, l_Lean_Elab_Deriving_mkImplicitBinders,
    l_Lean_Elab_Deriving_mkInductArgNames, l_Lean_Elab_Deriving_mkInductiveApp___redArg,
    l_Lean_Elab_Deriving_mkInstImplicitBinders,
    l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg,
    runtime_initialize_Lean_Elab_Deriving_Util,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::{l_Lean_isInductiveCore, l_Lean_isInductiveCore_x3f};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__0_value) as *mut leanh::LeanObject,16093780639914376387 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value) as *mut leanh::LeanObject,11450788041916860024 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__7_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__10_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__13_value) as *mut leanh::LeanObject,8497769072906204829 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__15_value) as *mut leanh::LeanObject,14557702332550915328 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18_value) as *mut leanh::LeanObject,11064845058293668901 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__20_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__22_value) as *mut leanh::LeanObject,5940551064397964566 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__24_value) as *mut leanh::LeanObject,4498178684837002829 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 101, 114, 101, 83, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__12_value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__27_value) as *mut leanh::LeanObject,7794500365561932708 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [119, 104, 101, 114, 101, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__30_value) as *mut leanh::LeanObject,5018042693327868416 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__32_value) as *mut leanh::LeanObject,6117808163008040242 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__34_value) as *mut leanh::LeanObject,14295752356045161913 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 102, 108, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36_value) as *mut leanh::LeanObject,17342663138809293389 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__39_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__41_value) as *mut leanh::LeanObject,7440505896048223825 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__44_value) as *mut leanh::LeanObject,16173796135615239867 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__48_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__47_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__50_value) as *mut leanh::LeanObject,17228437386856258271 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 72, 101, 108, 112, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__52_value) as *mut leanh::LeanObject,15296920709769342228 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__53_value) as *mut leanh::LeanObject,8670410953647023675 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 82, 101, 102, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 102, 108, 66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value) as *mut leanh::LeanObject,3113176348997436611 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__58_value) as *mut leanh::LeanObject,5231323067344049908 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__60_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_value: leanh::LeanStringObject<58> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 32, 96, 82, 101, 102, 108, 66, 69, 113, 96, 32, 102, 111, 114, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 115, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67_value: leanh::LeanStringObject<58> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 32, 96, 82, 101, 102, 108, 66, 69, 113, 96, 32, 102, 111, 114, 32, 109, 117, 116, 117, 97, 108, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 115, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value) as *mut leanh::LeanObject,5241190260012038858 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value) as *mut leanh::LeanObject,7333132211337544349 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,3856215070636856232 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,11539306374890340865 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value) as *mut leanh::LeanObject,10505514947164093791 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value) as *mut leanh::LeanObject,12089388034207105033 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value) as *mut leanh::LeanObject,5767257642920290930 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7435371527859266567 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9709290024534632994 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__4_value) as *mut leanh::LeanObject,14339263161491349763 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__56_value) as *mut leanh::LeanObject,8429561143893095733 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__57_value) as *mut leanh::LeanObject,14962380292094622331 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__2_value) as *mut leanh::LeanObject,3082180693422454072 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 333339820 as usize) << 1) | 1) as *mut leanh::LeanObject,10524666856273870862 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12959724626761231449 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3472278244867411345 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,11829213090506947180 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(
    mut v_msgData_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
    mut v___y_986_: *mut leanh::LeanObject,
    mut v___y_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = lean_st_ref_get(v___y_988_);
    v_env_991_ = leanh::lean_ctor_get(v___x_990_, 0);
    leanh::lean_inc_ref(v_env_991_);
    leanh::lean_dec(v___x_990_);
    v___x_992_ = lean_st_ref_get(v___y_986_);
    v_mctx_993_ = leanh::lean_ctor_get(v___x_992_, 0);
    leanh::lean_inc_ref(v_mctx_993_);
    leanh::lean_dec(v___x_992_);
    v_lctx_994_ = leanh::lean_ctor_get(v___y_985_, 2);
    v_options_995_ = leanh::lean_ctor_get(v___y_987_, 2);
    leanh::lean_inc_ref(v_options_995_);
    leanh::lean_inc_ref(v_lctx_994_);
    v___x_996_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_996_, 0, v_env_991_);
    leanh::lean_ctor_set(v___x_996_, 1, v_mctx_993_);
    leanh::lean_ctor_set(v___x_996_, 2, v_lctx_994_);
    leanh::lean_ctor_set(v___x_996_, 3, v_options_995_);
    v___x_997_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_997_, 0, v___x_996_);
    leanh::lean_ctor_set(v___x_997_, 1, v_msgData_984_);
    v___x_998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_998_, 0, v___x_997_);
    return v___x_998_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2___boxed(
    mut v_msgData_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1005_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msgData_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
    leanh::lean_dec(v___y_1003_);
    leanh::lean_dec_ref(v___y_1002_);
    leanh::lean_dec(v___y_1001_);
    leanh::lean_dec_ref(v___y_1000_);
    return v_res_1005_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: f64 = 0.0;
    v___x_1006_ = leanh::lean_unsigned_to_nat(0);
    v___x_1007_ = lean_float_of_nat(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(
    mut v_cls_1011_: *mut leanh::LeanObject,
    mut v_msg_1012_: *mut leanh::LeanObject,
    mut v___y_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v_tid_1037_: u64 = 0;
    let mut v_traces_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: f64 = 0.0;
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1062_: u8 = 0;
    let mut v_isSharedCheck_1063_: u8 = 0;
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1018_ = leanh::lean_ctor_get(v___y_1015_, 5);
                v___x_1019_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
                v_a_1020_ = leanh::lean_ctor_get(v___x_1019_, 0);
                v_isSharedCheck_1064_ = (!leanh::lean_is_exclusive(v___x_1019_)) as u8;
                if v_isSharedCheck_1064_ == 0 {
                    v___x_1022_ = v___x_1019_;
                    v_isShared_1023_ = v_isSharedCheck_1064_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1020_);
                    leanh::lean_dec(v___x_1019_);
                    v___x_1022_ = leanh::lean_box(0);
                    v_isShared_1023_ = v_isSharedCheck_1064_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1024_ = lean_st_ref_take(v___y_1016_);
                v_traceState_1025_ = leanh::lean_ctor_get(v___x_1024_, 4);
                v_env_1026_ = leanh::lean_ctor_get(v___x_1024_, 0);
                v_nextMacroScope_1027_ = leanh::lean_ctor_get(v___x_1024_, 1);
                v_ngen_1028_ = leanh::lean_ctor_get(v___x_1024_, 2);
                v_auxDeclNGen_1029_ = leanh::lean_ctor_get(v___x_1024_, 3);
                v_cache_1030_ = leanh::lean_ctor_get(v___x_1024_, 5);
                v_messages_1031_ = leanh::lean_ctor_get(v___x_1024_, 6);
                v_infoState_1032_ = leanh::lean_ctor_get(v___x_1024_, 7);
                v_snapshotTasks_1033_ = leanh::lean_ctor_get(v___x_1024_, 8);
                v_isSharedCheck_1063_ = (!leanh::lean_is_exclusive(v___x_1024_)) as u8;
                if v_isSharedCheck_1063_ == 0 {
                    v___x_1035_ = v___x_1024_;
                    v_isShared_1036_ = v_isSharedCheck_1063_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1033_);
                    leanh::lean_inc(v_infoState_1032_);
                    leanh::lean_inc(v_messages_1031_);
                    leanh::lean_inc(v_cache_1030_);
                    leanh::lean_inc(v_traceState_1025_);
                    leanh::lean_inc(v_auxDeclNGen_1029_);
                    leanh::lean_inc(v_ngen_1028_);
                    leanh::lean_inc(v_nextMacroScope_1027_);
                    leanh::lean_inc(v_env_1026_);
                    leanh::lean_dec(v___x_1024_);
                    v___x_1035_ = leanh::lean_box(0);
                    v_isShared_1036_ = v_isSharedCheck_1063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1037_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1025_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1038_ = leanh::lean_ctor_get(v_traceState_1025_, 0);
                v_isSharedCheck_1062_ =
                    (!leanh::lean_is_exclusive(v_traceState_1025_)) as u8;
                if v_isSharedCheck_1062_ == 0 {
                    v___x_1040_ = v_traceState_1025_;
                    v_isShared_1041_ = v_isSharedCheck_1062_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1038_);
                    leanh::lean_dec(v_traceState_1025_);
                    v___x_1040_ = leanh::lean_box(0);
                    v_isShared_1041_ = v_isSharedCheck_1062_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1042_ = leanh::lean_box(0);
                v___x_1043_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__0);
                v___x_1044_ = 0;
                v___x_1045_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__1;
                v___x_1046_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1046_, 0, v_cls_1011_);
                leanh::lean_ctor_set(v___x_1046_, 1, v___x_1042_);
                leanh::lean_ctor_set(v___x_1046_, 2, v___x_1045_);
                leanh::lean_ctor_set_float(
                    v___x_1046_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1043_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1046_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1043_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1046_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1044_,
                );
                v___x_1047_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___closed__2;
                v___x_1048_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1048_, 0, v___x_1046_);
                leanh::lean_ctor_set(v___x_1048_, 1, v_a_1020_);
                leanh::lean_ctor_set(v___x_1048_, 2, v___x_1047_);
                leanh::lean_inc(v_ref_1018_);
                v___x_1049_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1049_, 0, v_ref_1018_);
                leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
                v___x_1050_ = l_Lean_PersistentArray_push___redArg(v_traces_1038_, v___x_1049_);
                if v_isShared_1041_ == 0 {
                    leanh::lean_ctor_set(v___x_1040_, 0, v___x_1050_);
                    v___x_1052_ = v___x_1040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1061_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1050_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1061_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1037_,
                    );
                    v___x_1052_ = v_reuseFailAlloc_1061_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1036_ == 0 {
                    leanh::lean_ctor_set(v___x_1035_, 4, v___x_1052_);
                    v___x_1054_ = v___x_1035_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1060_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_env_1026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_nextMacroScope_1027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_ngen_1028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_auxDeclNGen_1029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___x_1052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 5, v_cache_1030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 6, v_messages_1031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 7, v_infoState_1032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1060_, 8, v_snapshotTasks_1033_);
                    v___x_1054_ = v_reuseFailAlloc_1060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1055_ = lean_st_ref_set(v___y_1016_, v___x_1054_);
                v___x_1056_ = leanh::lean_box(0);
                if v_isShared_1023_ == 0 {
                    leanh::lean_ctor_set(v___x_1022_, 0, v___x_1056_);
                    v___x_1058_ = v___x_1022_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg___boxed(
    mut v_cls_1065_: *mut leanh::LeanObject,
    mut v_msg_1066_: *mut leanh::LeanObject,
    mut v___y_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
    mut v___y_1070_: *mut leanh::LeanObject,
    mut v___y_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_1065_, v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
    leanh::lean_dec(v___y_1070_);
    leanh::lean_dec_ref(v___y_1069_);
    leanh::lean_dec(v___y_1068_);
    leanh::lean_dec_ref(v___y_1067_);
    return v_res_1072_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1073_) == 0 {
                    v___x_1075_ = l_List_reverse___redArg(v_a_1074_);
                    return v___x_1075_;
                } else {
                    v_head_1076_ = leanh::lean_ctor_get(v_a_1073_, 0);
                    v_tail_1077_ = leanh::lean_ctor_get(v_a_1073_, 1);
                    v_isSharedCheck_1086_ = (!leanh::lean_is_exclusive(v_a_1073_)) as u8;
                    if v_isSharedCheck_1086_ == 0 {
                        v___x_1079_ = v_a_1073_;
                        v_isShared_1080_ = v_isSharedCheck_1086_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1077_);
                        leanh::lean_inc(v_head_1076_);
                        leanh::lean_dec(v_a_1073_);
                        v___x_1079_ = leanh::lean_box(0);
                        v_isShared_1080_ = v_isSharedCheck_1086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1081_ = l_Lean_MessageData_ofSyntax(v_head_1076_);
                if v_isShared_1080_ == 0 {
                    leanh::lean_ctor_set(v___x_1079_, 1, v_a_1074_);
                    leanh::lean_ctor_set(v___x_1079_, 0, v___x_1081_);
                    v___x_1083_ = v___x_1079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_a_1074_);
                    v___x_1083_ = v_reuseFailAlloc_1085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1073_ = v_tail_1077_;
                v_a_1074_ = v___x_1083_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = leanh::lean_box(1);
    v___x_1088_ = l_Lean_MessageData_ofFormat(v___x_1087_);
    return v___x_1088_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1092_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2;
    v___x_1093_ = l_Lean_MessageData_ofFormat(v___x_1092_);
    return v___x_1093_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(
    mut v_x_1094_: *mut leanh::LeanObject,
    mut v_x_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v_before_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1117_: u8 = 0;
    let mut v_unused_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1095_) == 0 {
                    return v_x_1094_;
                } else {
                    v_head_1096_ = leanh::lean_ctor_get(v_x_1095_, 0);
                    v_tail_1097_ = leanh::lean_ctor_get(v_x_1095_, 1);
                    v_isSharedCheck_1119_ = (!leanh::lean_is_exclusive(v_x_1095_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1099_ = v_x_1095_;
                        v_isShared_1100_ = v_isSharedCheck_1119_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1097_);
                        leanh::lean_inc(v_head_1096_);
                        leanh::lean_dec(v_x_1095_);
                        v___x_1099_ = leanh::lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1101_ = leanh::lean_ctor_get(v_head_1096_, 0);
                v_isSharedCheck_1117_ = (!leanh::lean_is_exclusive(v_head_1096_)) as u8;
                if v_isSharedCheck_1117_ == 0 {
                    v_unused_1118_ = leanh::lean_ctor_get(v_head_1096_, 1);
                    leanh::lean_dec(v_unused_1118_);
                    v___x_1103_ = v_head_1096_;
                    v_isShared_1104_ = v_isSharedCheck_1117_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_1101_);
                    leanh::lean_dec(v_head_1096_);
                    v___x_1103_ = leanh::lean_box(0);
                    v_isShared_1104_ = v_isSharedCheck_1117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
                if v_isShared_1104_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1103_, 7);
                    leanh::lean_ctor_set(v___x_1103_, 1, v___x_1105_);
                    leanh::lean_ctor_set(v___x_1103_, 0, v_x_1094_);
                    v___x_1107_ = v___x_1103_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1116_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_x_1094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1105_);
                    v___x_1107_ = v_reuseFailAlloc_1116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1108_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
                if v_isShared_1100_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1099_, 7);
                    leanh::lean_ctor_set(v___x_1099_, 1, v___x_1108_);
                    leanh::lean_ctor_set(v___x_1099_, 0, v___x_1107_);
                    v___x_1110_ = v___x_1099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1108_);
                    v___x_1110_ = v_reuseFailAlloc_1115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1111_ = l_Lean_MessageData_ofSyntax(v_before_1101_);
                v___x_1112_ = l_Lean_indentD(v___x_1111_);
                v___x_1113_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1113_, 0, v___x_1110_);
                leanh::lean_ctor_set(v___x_1113_, 1, v___x_1112_);
                v_x_1094_ = v___x_1113_;
                v_x_1095_ = v_tail_1097_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(
    mut v_opts_1120_: *mut leanh::LeanObject,
    mut v_opt_1121_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1122_ = leanh::lean_ctor_get(v_opt_1121_, 0);
    v_defValue_1123_ = leanh::lean_ctor_get(v_opt_1121_, 1);
    v_map_1124_ = leanh::lean_ctor_get(v_opts_1120_, 0);
    v___x_1125_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1124_,
            v_name_1122_,
        );
    if leanh::lean_obj_tag(v___x_1125_) == 0 {
        let mut v___x_1126_: u8 = 0;
        v___x_1126_ = (leanh::lean_unbox(v_defValue_1123_) as u8);
        return v___x_1126_;
    } else {
        let mut v_val_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1127_ = leanh::lean_ctor_get(v___x_1125_, 0);
        leanh::lean_inc(v_val_1127_);
        leanh::lean_dec_ref_known(v___x_1125_, 1);
        if leanh::lean_obj_tag(v_val_1127_) == 1 {
            let mut v_v_1128_: u8 = 0;
            v_v_1128_ = leanh::lean_ctor_get_uint8(v_val_1127_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1127_, 0);
            return v_v_1128_;
        } else {
            let mut v___x_1129_: u8 = 0;
            leanh::lean_dec(v_val_1127_);
            v___x_1129_ = (leanh::lean_unbox(v_defValue_1123_) as u8);
            return v___x_1129_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(
    mut v_opts_1130_: *mut leanh::LeanObject,
    mut v_opt_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1132_: u8 = 0;
    let mut v_r_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_1130_, v_opt_1131_);
    leanh::lean_dec_ref(v_opt_1131_);
    leanh::lean_dec_ref(v_opts_1130_);
    v_r_1133_ = leanh::lean_box((v_res_1132_) as usize);
    return v_r_1133_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1137_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__1;
    v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
    return v___x_1138_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(
    mut v_msgData_1139_: *mut leanh::LeanObject,
    mut v_macroStack_1140_: *mut leanh::LeanObject,
    mut v___y_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v_unused_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1143_ = leanh::lean_ctor_get(v___y_1141_, 2);
                v___x_1144_ = l_Lean_Elab_pp_macroStack;
                v___x_1145_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__5(v_options_1143_, v___x_1144_);
                if v___x_1145_ == 0 {
                    leanh::lean_dec(v_macroStack_1140_);
                    v___x_1146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1146_, 0, v_msgData_1139_);
                    return v___x_1146_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_1140_) == 0 {
                        v___x_1147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1147_, 0, v_msgData_1139_);
                        return v___x_1147_;
                    } else {
                        v_head_1148_ = leanh::lean_ctor_get(v_macroStack_1140_, 0);
                        leanh::lean_inc(v_head_1148_);
                        v_after_1149_ = leanh::lean_ctor_get(v_head_1148_, 1);
                        v_isSharedCheck_1164_ =
                            (!leanh::lean_is_exclusive(v_head_1148_)) as u8;
                        if v_isSharedCheck_1164_ == 0 {
                            v_unused_1165_ = leanh::lean_ctor_get(v_head_1148_, 0);
                            leanh::lean_dec(v_unused_1165_);
                            v___x_1151_ = v_head_1148_;
                            v_isShared_1152_ = v_isSharedCheck_1164_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_1149_);
                            leanh::lean_dec(v_head_1148_);
                            v___x_1151_ = leanh::lean_box(0);
                            v_isShared_1152_ = v_isSharedCheck_1164_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1153_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
                if v_isShared_1152_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1151_, 7);
                    leanh::lean_ctor_set(v___x_1151_, 1, v___x_1153_);
                    leanh::lean_ctor_set(v___x_1151_, 0, v_msgData_1139_);
                    v___x_1155_ = v___x_1151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1163_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_msgData_1139_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1163_, 1, v___x_1153_);
                    v___x_1155_ = v_reuseFailAlloc_1163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1156_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
                v___x_1157_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1157_, 0, v___x_1155_);
                leanh::lean_ctor_set(v___x_1157_, 1, v___x_1156_);
                v___x_1158_ = l_Lean_MessageData_ofSyntax(v_after_1149_);
                v___x_1159_ = l_Lean_indentD(v___x_1158_);
                v_msgData_1160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_1160_, 0, v___x_1157_);
                leanh::lean_ctor_set(v_msgData_1160_, 1, v___x_1159_);
                v___x_1161_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_1160_, v_macroStack_1140_);
                v___x_1162_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                return v___x_1162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg___boxed(
    mut v_msgData_1166_: *mut leanh::LeanObject,
    mut v_macroStack_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1170_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_1166_, v_macroStack_1167_, v___y_1168_);
    leanh::lean_dec_ref(v___y_1168_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(
    mut v_msg_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1179_ = leanh::lean_ctor_get(v___y_1176_, 5);
                v___x_1180_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2_spec__2(v_msg_1171_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
                v_a_1181_ = leanh::lean_ctor_get(v___x_1180_, 0);
                leanh::lean_inc(v_a_1181_);
                leanh::lean_dec_ref(v___x_1180_);
                v_macroStack_1182_ = leanh::lean_ctor_get(v___y_1172_, 1);
                v___x_1183_ = l_Lean_Elab_getBetterRef(v_ref_1179_, v_macroStack_1182_);
                leanh::lean_inc(v_macroStack_1182_);
                v___x_1184_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_a_1181_, v_macroStack_1182_, v___y_1176_);
                v_a_1185_ = leanh::lean_ctor_get(v___x_1184_, 0);
                v_isSharedCheck_1193_ = (!leanh::lean_is_exclusive(v___x_1184_)) as u8;
                if v_isSharedCheck_1193_ == 0 {
                    v___x_1187_ = v___x_1184_;
                    v_isShared_1188_ = v_isSharedCheck_1193_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1185_);
                    leanh::lean_dec(v___x_1184_);
                    v___x_1187_ = leanh::lean_box(0);
                    v_isShared_1188_ = v_isSharedCheck_1193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1189_, 0, v___x_1183_);
                leanh::lean_ctor_set(v___x_1189_, 1, v_a_1185_);
                if v_isShared_1188_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1187_, 1);
                    leanh::lean_ctor_set(v___x_1187_, 0, v___x_1189_);
                    v___x_1191_ = v___x_1187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
                    v___x_1191_ = v_reuseFailAlloc_1192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg___boxed(
    mut v_msg_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
    mut v___y_1198_: *mut leanh::LeanObject,
    mut v___y_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1202_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
    leanh::lean_dec(v___y_1200_);
    leanh::lean_dec_ref(v___y_1199_);
    leanh::lean_dec(v___y_1198_);
    leanh::lean_dec_ref(v___y_1197_);
    leanh::lean_dec(v___y_1196_);
    leanh::lean_dec_ref(v___y_1195_);
    return v_res_1202_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__0;
    v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
    return v___x_1205_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__2;
    v___x_1208_ = l_Lean_stringToMessageData(v___x_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(
    mut v_constName_1209_: *mut leanh::LeanObject,
    mut v___y_1210_: *mut leanh::LeanObject,
    mut v___y_1211_: *mut leanh::LeanObject,
    mut v___y_1212_: *mut leanh::LeanObject,
    mut v___y_1213_: *mut leanh::LeanObject,
    mut v___y_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u8 = 0;
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1217_ = lean_st_ref_get(v___y_1215_);
                v_env_1218_ = leanh::lean_ctor_get(v___x_1217_, 0);
                leanh::lean_inc_ref(v_env_1218_);
                leanh::lean_dec(v___x_1217_);
                leanh::lean_inc(v_constName_1209_);
                v___x_1219_ = l_Lean_isInductiveCore_x3f(v_env_1218_, v_constName_1209_);
                if leanh::lean_obj_tag(v___x_1219_) == 0 {
                    v___x_1220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__1);
                    v___x_1221_ = 0;
                    v___x_1222_ = l_Lean_MessageData_ofConstName(v_constName_1209_, v___x_1221_);
                    v___x_1223_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1223_, 0, v___x_1220_);
                    leanh::lean_ctor_set(v___x_1223_, 1, v___x_1222_);
                    v___x_1224_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___closed__3);
                    v___x_1225_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1225_, 0, v___x_1223_);
                    leanh::lean_ctor_set(v___x_1225_, 1, v___x_1224_);
                    v___x_1226_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_1225_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
                    return v___x_1226_;
                } else {
                    leanh::lean_dec(v_constName_1209_);
                    v_val_1227_ = leanh::lean_ctor_get(v___x_1219_, 0);
                    v_isSharedCheck_1234_ = (!leanh::lean_is_exclusive(v___x_1219_)) as u8;
                    if v_isSharedCheck_1234_ == 0 {
                        v___x_1229_ = v___x_1219_;
                        v_isShared_1230_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1227_);
                        leanh::lean_dec(v___x_1219_);
                        v___x_1229_ = leanh::lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1230_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1229_, 0);
                    v___x_1232_ = v___x_1229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_val_1227_);
                    v___x_1232_ = v_reuseFailAlloc_1233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0___boxed(
    mut v_constName_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_constName_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
    leanh::lean_dec(v___y_1241_);
    leanh::lean_dec_ref(v___y_1240_);
    leanh::lean_dec(v___y_1239_);
    leanh::lean_dec_ref(v___y_1238_);
    leanh::lean_dec(v___y_1237_);
    leanh::lean_dec_ref(v___y_1236_);
    return v_res_1243_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1259_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3;
    v___x_1260_ = l_Lean_mkCIdent(v___x_1259_);
    return v___x_1260_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1277_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__36;
    v___x_1330_ = l_String_toRawSubstring_x27(v___x_1329_);
    return v___x_1330_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62()
-> *mut leanh::LeanObject {
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1382_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59;
    v___x_1383_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__61;
    v___x_1384_ = l_Lean_Name_append(v___x_1383_, v___x_1382_);
    return v___x_1384_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64()
-> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__63;
    v___x_1387_ = l_Lean_stringToMessageData(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66()
-> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__65;
    v___x_1390_ = l_Lean_stringToMessageData(v___x_1389_);
    return v___x_1390_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68()
-> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__67;
    v___x_1393_ = l_Lean_stringToMessageData(v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(
    mut v_declName_1394_: *mut leanh::LeanObject,
    mut v_a_1395_: *mut leanh::LeanObject,
    mut v_a_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
    mut v_a_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v_options_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1494_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_unused_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_a_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1534_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut v_a_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_a_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut v___y_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_all_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1586_: u8 = 0;
    let mut v_a_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1590_: u8 = 0;
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1402_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__0(v_declName_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
                if leanh::lean_obj_tag(v___x_1402_) == 0 {
                    v_a_1403_ = leanh::lean_ctor_get(v___x_1402_, 0);
                    leanh::lean_inc(v_a_1403_);
                    leanh::lean_dec_ref_known(v___x_1402_, 1);
                    v_all_1573_ = leanh::lean_ctor_get(v_a_1403_, 3);
                    v___x_1574_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1575_ = l_List_lengthTR___redArg(v_all_1573_);
                    v___x_1576_ = lean_nat_dec_lt(v___x_1574_, v___x_1575_);
                    leanh::lean_dec(v___x_1575_);
                    if v___x_1576_ == 0 {
                        v___y_1556_ = v_a_1395_;
                        v___y_1557_ = v_a_1396_;
                        v___y_1558_ = v_a_1397_;
                        v___y_1559_ = v_a_1398_;
                        v___y_1560_ = v_a_1399_;
                        v___y_1561_ = v_a_1400_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_1403_);
                        v___x_1577_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__68);
                        v___x_1578_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_1577_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
                        v_a_1579_ = leanh::lean_ctor_get(v___x_1578_, 0);
                        v_isSharedCheck_1586_ =
                            (!leanh::lean_is_exclusive(v___x_1578_)) as u8;
                        if v_isSharedCheck_1586_ == 0 {
                            v___x_1581_ = v___x_1578_;
                            v_isShared_1582_ = v_isSharedCheck_1586_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1579_);
                            leanh::lean_dec(v___x_1578_);
                            v___x_1581_ = leanh::lean_box(0);
                            v_isShared_1582_ = v_isSharedCheck_1586_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    v_a_1587_ = leanh::lean_ctor_get(v___x_1402_, 0);
                    v_isSharedCheck_1594_ = (!leanh::lean_is_exclusive(v___x_1402_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1589_ = v___x_1402_;
                        v_isShared_1590_ = v_isSharedCheck_1594_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1587_);
                        leanh::lean_dec(v___x_1402_);
                        v___x_1589_ = leanh::lean_box(0);
                        v_isShared_1590_ = v_isSharedCheck_1594_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1403_);
                v___x_1411_ = l_Lean_Elab_Deriving_mkInductArgNames(
                    v_a_1403_,
                    v___y_1405_,
                    v___y_1406_,
                    v___y_1407_,
                    v___y_1408_,
                    v___y_1409_,
                    v___y_1410_,
                );
                if leanh::lean_obj_tag(v___x_1411_) == 0 {
                    v_a_1412_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    leanh::lean_inc_n(v_a_1412_, 2);
                    leanh::lean_dec_ref_known(v___x_1411_, 1);
                    v___x_1413_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                        v_a_1412_,
                        v___y_1405_,
                        v___y_1406_,
                        v___y_1407_,
                        v___y_1408_,
                        v___y_1409_,
                        v___y_1410_,
                    );
                    if leanh::lean_obj_tag(v___x_1413_) == 0 {
                        v_a_1414_ = leanh::lean_ctor_get(v___x_1413_, 0);
                        leanh::lean_inc(v_a_1414_);
                        leanh::lean_dec_ref_known(v___x_1413_, 1);
                        v___x_1415_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__1;
                        leanh::lean_inc(v_a_1412_);
                        leanh::lean_inc(v_a_1403_);
                        v___x_1416_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                            v___x_1415_,
                            v_a_1403_,
                            v_a_1412_,
                            v___y_1405_,
                            v___y_1406_,
                            v___y_1407_,
                            v___y_1408_,
                            v___y_1409_,
                            v___y_1410_,
                        );
                        if leanh::lean_obj_tag(v___x_1416_) == 0 {
                            v_a_1417_ = leanh::lean_ctor_get(v___x_1416_, 0);
                            leanh::lean_inc(v_a_1417_);
                            leanh::lean_dec_ref_known(v___x_1416_, 1);
                            v___x_1418_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3;
                            leanh::lean_inc(v_a_1412_);
                            leanh::lean_inc(v_a_1403_);
                            v___x_1419_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                                v___x_1418_,
                                v_a_1403_,
                                v_a_1412_,
                                v___y_1405_,
                                v___y_1406_,
                                v___y_1407_,
                                v___y_1408_,
                                v___y_1409_,
                                v___y_1410_,
                            );
                            if leanh::lean_obj_tag(v___x_1419_) == 0 {
                                v_a_1420_ = leanh::lean_ctor_get(v___x_1419_, 0);
                                leanh::lean_inc(v_a_1420_);
                                leanh::lean_dec_ref_known(v___x_1419_, 1);
                                v___x_1421_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                    v_a_1403_,
                                    v_a_1412_,
                                    v___y_1409_,
                                );
                                if leanh::lean_obj_tag(v___x_1421_) == 0 {
                                    v_a_1422_ = leanh::lean_ctor_get(v___x_1421_, 0);
                                    v_isSharedCheck_1530_ =
                                        (!leanh::lean_is_exclusive(v___x_1421_)) as u8;
                                    if v_isSharedCheck_1530_ == 0 {
                                        v___x_1424_ = v___x_1421_;
                                        v_isShared_1425_ = v_isSharedCheck_1530_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1422_);
                                        leanh::lean_dec(v___x_1421_);
                                        v___x_1424_ = leanh::lean_box(0);
                                        v_isShared_1425_ = v_isSharedCheck_1530_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1420_);
                                    leanh::lean_dec(v_a_1417_);
                                    leanh::lean_dec(v_a_1414_);
                                    v_a_1531_ = leanh::lean_ctor_get(v___x_1421_, 0);
                                    v_isSharedCheck_1538_ =
                                        (!leanh::lean_is_exclusive(v___x_1421_)) as u8;
                                    if v_isSharedCheck_1538_ == 0 {
                                        v___x_1533_ = v___x_1421_;
                                        v_isShared_1534_ = v_isSharedCheck_1538_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1531_);
                                        leanh::lean_dec(v___x_1421_);
                                        v___x_1533_ = leanh::lean_box(0);
                                        v_isShared_1534_ = v_isSharedCheck_1538_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_1417_);
                                leanh::lean_dec(v_a_1414_);
                                leanh::lean_dec(v_a_1412_);
                                leanh::lean_dec(v_a_1403_);
                                return v___x_1419_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1414_);
                            leanh::lean_dec(v_a_1412_);
                            leanh::lean_dec(v_a_1403_);
                            return v___x_1416_;
                        }
                    } else {
                        leanh::lean_dec(v_a_1412_);
                        leanh::lean_dec(v_a_1403_);
                        v_a_1539_ = leanh::lean_ctor_get(v___x_1413_, 0);
                        v_isSharedCheck_1546_ =
                            (!leanh::lean_is_exclusive(v___x_1413_)) as u8;
                        if v_isSharedCheck_1546_ == 0 {
                            v___x_1541_ = v___x_1413_;
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1539_);
                            leanh::lean_dec(v___x_1413_);
                            v___x_1541_ = leanh::lean_box(0);
                            v_isShared_1542_ = v_isSharedCheck_1546_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1403_);
                    v_a_1547_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1554_ = (!leanh::lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1554_ == 0 {
                        v___x_1549_ = v___x_1411_;
                        v_isShared_1550_ = v_isSharedCheck_1554_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1547_);
                        leanh::lean_dec(v___x_1411_);
                        v___x_1549_ = leanh::lean_box(0);
                        v_isShared_1550_ = v_isSharedCheck_1554_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_options_1426_ = leanh::lean_ctor_get(v___y_1409_, 2);
                v_ref_1427_ = leanh::lean_ctor_get(v___y_1409_, 5);
                v_quotContext_1428_ = leanh::lean_ctor_get(v___y_1409_, 10);
                v_currMacroScope_1429_ = leanh::lean_ctor_get(v___y_1409_, 11);
                v_inheritedTraceOptions_1430_ = leanh::lean_ctor_get(v___y_1409_, 13);
                v___x_1431_ = l_Array_append___redArg(v_a_1414_, v_a_1417_);
                leanh::lean_dec(v_a_1417_);
                v___x_1432_ = l_Array_append___redArg(v___x_1431_, v_a_1420_);
                leanh::lean_dec(v_a_1420_);
                v___x_1433_ = 0;
                v___x_1434_ = l_Lean_SourceInfo_fromRef(v_ref_1427_, v___x_1433_);
                v___x_1435_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__8;
                v___x_1436_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__9);
                v___x_1437_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__11;
                leanh::lean_inc_n(v___x_1434_, 28);
                v___x_1438_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1437_, v_a_1422_);
                v___x_1439_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1435_, v___x_1436_, v___x_1438_);
                v___x_1440_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__14;
                v___x_1441_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__16;
                v___x_1442_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__17);
                v___x_1443_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1443_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1443_, 1, v___x_1437_);
                leanh::lean_ctor_set(v___x_1443_, 2, v___x_1442_);
                leanh::lean_inc_ref_n(v___x_1443_, 14);
                v___x_1444_ = l_Lean_Syntax_node7(
                    v___x_1434_,
                    v___x_1441_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1443_,
                );
                v___x_1445_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__18;
                v___x_1446_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__19;
                v___x_1447_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__21;
                v___x_1448_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1447_, v___x_1443_);
                v___x_1449_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1449_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1449_, 1, v___x_1445_);
                v___x_1450_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__23;
                v___x_1451_ = l_Array_append___redArg(v___x_1442_, v___x_1432_);
                leanh::lean_dec_ref(v___x_1432_);
                v___x_1452_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1452_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1452_, 1, v___x_1437_);
                leanh::lean_ctor_set(v___x_1452_, 2, v___x_1451_);
                v___x_1453_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__25;
                v___x_1454_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__26;
                v___x_1455_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1455_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1455_, 1, v___x_1454_);
                v___x_1456_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1453_, v___x_1455_, v___x_1439_);
                v___x_1457_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1450_, v___x_1452_, v___x_1456_);
                v___x_1458_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__28;
                v___x_1459_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__29;
                v___x_1460_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1460_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1460_, 1, v___x_1459_);
                v___x_1461_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__31;
                v___x_1462_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__33;
                v___x_1463_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__35;
                v___x_1464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__37);
                v___x_1465_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__38;
                leanh::lean_inc(v_currMacroScope_1429_);
                leanh::lean_inc(v_quotContext_1428_);
                v___x_1466_ =
                    l_Lean_addMacroScope(v_quotContext_1428_, v___x_1465_, v_currMacroScope_1429_);
                v___x_1467_ = leanh::lean_box(0);
                v___x_1468_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__40;
                v___x_1469_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1469_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1469_, 1, v___x_1464_);
                leanh::lean_ctor_set(v___x_1469_, 2, v___x_1466_);
                leanh::lean_ctor_set(v___x_1469_, 3, v___x_1468_);
                v___x_1470_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1463_, v___x_1469_, v___x_1443_);
                v___x_1471_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__42;
                v___x_1472_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__43;
                v___x_1473_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1473_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1473_, 1, v___x_1472_);
                v___x_1474_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__45;
                v___x_1475_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__46;
                v___x_1476_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1476_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1476_, 1, v___x_1475_);
                v___x_1477_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__49;
                v___x_1478_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__51;
                v___x_1479_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__54;
                v___x_1480_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__55;
                v___x_1481_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1481_, 0, v___x_1434_);
                leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                v___x_1482_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1479_, v___x_1481_);
                v___x_1483_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1437_, v___x_1482_);
                v___x_1484_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1478_, v___x_1483_);
                v___x_1485_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1477_, v___x_1484_);
                v___x_1486_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1474_, v___x_1476_, v___x_1485_);
                v___x_1487_ = l_Lean_Syntax_node3(
                    v___x_1434_,
                    v___x_1471_,
                    v___x_1473_,
                    v___x_1443_,
                    v___x_1486_,
                );
                v___x_1488_ = l_Lean_Syntax_node3(
                    v___x_1434_,
                    v___x_1437_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1487_,
                );
                v___x_1489_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1462_, v___x_1470_, v___x_1488_);
                v___x_1490_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1437_, v___x_1489_);
                v___x_1491_ = l_Lean_Syntax_node1(v___x_1434_, v___x_1461_, v___x_1490_);
                v___x_1492_ = l_Lean_Syntax_node3(
                    v___x_1434_,
                    v___x_1458_,
                    v___x_1460_,
                    v___x_1491_,
                    v___x_1443_,
                );
                v___x_1493_ = l_Lean_Syntax_node6(
                    v___x_1434_,
                    v___x_1446_,
                    v___x_1448_,
                    v___x_1449_,
                    v___x_1443_,
                    v___x_1443_,
                    v___x_1457_,
                    v___x_1492_,
                );
                v_hasTrace_1494_ = leanh::lean_ctor_get_uint8(
                    v_options_1426_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_1495_ =
                    l_Lean_Syntax_node2(v___x_1434_, v___x_1440_, v___x_1444_, v___x_1493_);
                v___x_1496_ = leanh::lean_unsigned_to_nat(1);
                v___x_1497_ = lean_mk_empty_array_with_capacity(v___x_1496_);
                v___x_1498_ = lean_array_push(v___x_1497_, v___x_1495_);
                if v_hasTrace_1494_ == 0 {
                    if v_isShared_1425_ == 0 {
                        leanh::lean_ctor_set(v___x_1424_, 0, v___x_1498_);
                        v___x_1500_ = v___x_1424_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
                        v___x_1500_ = v_reuseFailAlloc_1501_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1502_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59;
                    v___x_1503_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__62);
                    v___x_1504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1430_,
                        v_options_1426_,
                        v___x_1503_,
                    );
                    if v___x_1504_ == 0 {
                        if v_isShared_1425_ == 0 {
                            leanh::lean_ctor_set(v___x_1424_, 0, v___x_1498_);
                            v___x_1506_ = v___x_1424_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1507_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1498_);
                            v___x_1506_ = v_reuseFailAlloc_1507_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1424_);
                        v___x_1508_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__64);
                        leanh::lean_inc_ref(v___x_1498_);
                        v___x_1509_ = lean_array_to_list(v___x_1498_);
                        v___x_1510_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__1(v___x_1509_, v___x_1467_);
                        v___x_1511_ = l_Lean_MessageData_ofList(v___x_1510_);
                        v___x_1512_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1512_, 0, v___x_1508_);
                        leanh::lean_ctor_set(v___x_1512_, 1, v___x_1511_);
                        v___x_1513_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v___x_1502_, v___x_1512_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
                        if leanh::lean_obj_tag(v___x_1513_) == 0 {
                            v_isSharedCheck_1520_ =
                                (!leanh::lean_is_exclusive(v___x_1513_)) as u8;
                            if v_isSharedCheck_1520_ == 0 {
                                v_unused_1521_ = leanh::lean_ctor_get(v___x_1513_, 0);
                                leanh::lean_dec(v_unused_1521_);
                                v___x_1515_ = v___x_1513_;
                                v_isShared_1516_ = v_isSharedCheck_1520_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1513_);
                                v___x_1515_ = leanh::lean_box(0);
                                v_isShared_1516_ = v_isSharedCheck_1520_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1498_);
                            v_a_1522_ = leanh::lean_ctor_get(v___x_1513_, 0);
                            v_isSharedCheck_1529_ =
                                (!leanh::lean_is_exclusive(v___x_1513_)) as u8;
                            if v_isSharedCheck_1529_ == 0 {
                                v___x_1524_ = v___x_1513_;
                                v_isShared_1525_ = v_isSharedCheck_1529_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1522_);
                                leanh::lean_dec(v___x_1513_);
                                v___x_1524_ = leanh::lean_box(0);
                                v_isShared_1525_ = v_isSharedCheck_1529_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_1500_;
            }
            4 => {
                return v___x_1506_;
            }
            5 => {
                if v_isShared_1516_ == 0 {
                    leanh::lean_ctor_set(v___x_1515_, 0, v___x_1498_);
                    v___x_1518_ = v___x_1515_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1498_);
                    v___x_1518_ = v_reuseFailAlloc_1519_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1518_;
            }
            7 => {
                if v_isShared_1525_ == 0 {
                    v___x_1527_ = v___x_1524_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
                    v___x_1527_ = v_reuseFailAlloc_1528_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1527_;
            }
            9 => {
                if v_isShared_1534_ == 0 {
                    v___x_1536_ = v___x_1533_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
                    v___x_1536_ = v_reuseFailAlloc_1537_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1536_;
            }
            11 => {
                if v_isShared_1542_ == 0 {
                    v___x_1544_ = v___x_1541_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1544_;
            }
            13 => {
                if v_isShared_1550_ == 0 {
                    v___x_1552_ = v___x_1549_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
                    v___x_1552_ = v_reuseFailAlloc_1553_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1552_;
            }
            15 => {
                v___x_1562_ = l_Lean_InductiveVal_isNested(v_a_1403_);
                if v___x_1562_ == 0 {
                    v___y_1405_ = v___y_1556_;
                    v___y_1406_ = v___y_1557_;
                    v___y_1407_ = v___y_1558_;
                    v___y_1408_ = v___y_1559_;
                    v___y_1409_ = v___y_1560_;
                    v___y_1410_ = v___y_1561_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_1403_);
                    v___x_1563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66_once), _init_l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__66);
                    v___x_1564_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v___x_1563_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
                    v_a_1565_ = leanh::lean_ctor_get(v___x_1564_, 0);
                    v_isSharedCheck_1572_ = (!leanh::lean_is_exclusive(v___x_1564_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1567_ = v___x_1564_;
                        v_isShared_1568_ = v_isSharedCheck_1572_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1565_);
                        leanh::lean_dec(v___x_1564_);
                        v___x_1567_ = leanh::lean_box(0);
                        v_isShared_1568_ = v_isSharedCheck_1572_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_1568_ == 0 {
                    v___x_1570_ = v___x_1567_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1570_;
            }
            18 => {
                if v_isShared_1582_ == 0 {
                    v___x_1584_ = v___x_1581_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
                    v___x_1584_ = v_reuseFailAlloc_1585_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1584_;
            }
            20 => {
                if v_isShared_1590_ == 0 {
                    v___x_1592_ = v___x_1589_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed(
    mut v_declName_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
    mut v_a_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
    mut v_a_1600_: *mut leanh::LeanObject,
    mut v_a_1601_: *mut leanh::LeanObject,
    mut v_a_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ =
        l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds(
            v_declName_1595_,
            v_a_1596_,
            v_a_1597_,
            v_a_1598_,
            v_a_1599_,
            v_a_1600_,
            v_a_1601_,
        );
    leanh::lean_dec(v_a_1601_);
    leanh::lean_dec_ref(v_a_1600_);
    leanh::lean_dec(v_a_1599_);
    leanh::lean_dec_ref(v_a_1598_);
    leanh::lean_dec(v_a_1597_);
    leanh::lean_dec_ref(v_a_1596_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(
    mut v_cls_1604_: *mut leanh::LeanObject,
    mut v_msg_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
    mut v___y_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___redArg(v_cls_1604_, v_msg_1605_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2___boxed(
    mut v_cls_1614_: *mut leanh::LeanObject,
    mut v_msg_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
    mut v___y_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__2(v_cls_1614_, v_msg_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
    leanh::lean_dec(v___y_1621_);
    leanh::lean_dec_ref(v___y_1620_);
    leanh::lean_dec(v___y_1619_);
    leanh::lean_dec_ref(v___y_1618_);
    leanh::lean_dec(v___y_1617_);
    leanh::lean_dec_ref(v___y_1616_);
    return v_res_1623_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(
    mut v_00_u03b1_1624_: *mut leanh::LeanObject,
    mut v_msg_1625_: *mut leanh::LeanObject,
    mut v___y_1626_: *mut leanh::LeanObject,
    mut v___y_1627_: *mut leanh::LeanObject,
    mut v___y_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___redArg(v_msg_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
    return v___x_1633_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3___boxed(
    mut v_00_u03b1_1634_: *mut leanh::LeanObject,
    mut v_msg_1635_: *mut leanh::LeanObject,
    mut v___y_1636_: *mut leanh::LeanObject,
    mut v___y_1637_: *mut leanh::LeanObject,
    mut v___y_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3(v_00_u03b1_1634_, v_msg_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
    leanh::lean_dec(v___y_1641_);
    leanh::lean_dec_ref(v___y_1640_);
    leanh::lean_dec(v___y_1639_);
    leanh::lean_dec_ref(v___y_1638_);
    leanh::lean_dec(v___y_1637_);
    leanh::lean_dec_ref(v___y_1636_);
    return v_res_1643_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(
    mut v_msgData_1644_: *mut leanh::LeanObject,
    mut v_macroStack_1645_: *mut leanh::LeanObject,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
    mut v___y_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_1644_, v_macroStack_1645_, v___y_1650_);
    return v___x_1653_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4___boxed(
    mut v_msgData_1654_: *mut leanh::LeanObject,
    mut v_macroStack_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds_spec__3_spec__4(v_msgData_1654_, v_macroStack_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    leanh::lean_dec(v___y_1661_);
    leanh::lean_dec_ref(v___y_1660_);
    leanh::lean_dec(v___y_1659_);
    leanh::lean_dec_ref(v___y_1658_);
    leanh::lean_dec(v___y_1657_);
    leanh::lean_dec_ref(v___y_1656_);
    return v_res_1663_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(
    mut v_as_1664_: *mut leanh::LeanObject,
    mut v_i_1665_: usize,
    mut v_stop_1666_: usize,
    mut v_b_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: usize = 0;
    let mut v___x_1676_: usize = 0;
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1671_ = lean_usize_dec_eq(v_i_1665_, v_stop_1666_);
                if v___x_1671_ == 0 {
                    v___x_1672_ = lean_array_uget_borrowed(v_as_1664_, v_i_1665_);
                    leanh::lean_inc(v___x_1672_);
                    v___x_1673_ =
                        l_Lean_Elab_Command_elabCommand(v___x_1672_, v___y_1668_, v___y_1669_);
                    if leanh::lean_obj_tag(v___x_1673_) == 0 {
                        v_a_1674_ = leanh::lean_ctor_get(v___x_1673_, 0);
                        leanh::lean_inc(v_a_1674_);
                        leanh::lean_dec_ref_known(v___x_1673_, 1);
                        v___x_1675_ = 1usize;
                        v___x_1676_ = lean_usize_add(v_i_1665_, v___x_1675_);
                        v_i_1665_ = v___x_1676_;
                        v_b_1667_ = v_a_1674_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1673_;
                    }
                } else {
                    v___x_1678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1678_, 0, v_b_1667_);
                    return v___x_1678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0___boxed(
    mut v_as_1679_: *mut leanh::LeanObject,
    mut v_i_1680_: *mut leanh::LeanObject,
    mut v_stop_1681_: *mut leanh::LeanObject,
    mut v_b_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1686_: usize = 0;
    let mut v_stop_boxed_1687_: usize = 0;
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1686_ = leanh::lean_unbox_usize(v_i_1680_);
    leanh::lean_dec(v_i_1680_);
    v_stop_boxed_1687_ = leanh::lean_unbox_usize(v_stop_1681_);
    leanh::lean_dec(v_stop_1681_);
    v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_as_1679_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1682_, v___y_1683_, v___y_1684_);
    leanh::lean_dec(v___y_1684_);
    leanh::lean_dec_ref(v___y_1683_);
    leanh::lean_dec_ref(v_as_1679_);
    return v_res_1688_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(
    mut v___x_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1697_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: usize = 0;
    let mut v___x_1710_: usize = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: usize = 0;
    let mut v___x_1713_: usize = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1715_: u8 = 0;
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1693_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___x_1689_,
                    v___y_1690_,
                    v___y_1691_,
                );
                if leanh::lean_obj_tag(v___x_1693_) == 0 {
                    v_a_1694_ = leanh::lean_ctor_get(v___x_1693_, 0);
                    v_isSharedCheck_1715_ = (!leanh::lean_is_exclusive(v___x_1693_)) as u8;
                    if v_isSharedCheck_1715_ == 0 {
                        v___x_1696_ = v___x_1693_;
                        v_isShared_1697_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1694_);
                        leanh::lean_dec(v___x_1693_);
                        v___x_1696_ = leanh::lean_box(0);
                        v_isShared_1697_ = v_isSharedCheck_1715_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1716_ = leanh::lean_ctor_get(v___x_1693_, 0);
                    v_isSharedCheck_1723_ = (!leanh::lean_is_exclusive(v___x_1693_)) as u8;
                    if v_isSharedCheck_1723_ == 0 {
                        v___x_1718_ = v___x_1693_;
                        v_isShared_1719_ = v_isSharedCheck_1723_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1716_);
                        leanh::lean_dec(v___x_1693_);
                        v___x_1718_ = leanh::lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1723_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1698_ = leanh::lean_unsigned_to_nat(0);
                v___x_1699_ = lean_array_get_size(v_a_1694_);
                v___x_1700_ = leanh::lean_box(0);
                v___x_1701_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
                if v___x_1701_ == 0 {
                    leanh::lean_dec(v_a_1694_);
                    if v_isShared_1697_ == 0 {
                        leanh::lean_ctor_set(v___x_1696_, 0, v___x_1700_);
                        v___x_1703_ = v___x_1696_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1704_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1700_);
                        v___x_1703_ = v_reuseFailAlloc_1704_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1705_ = lean_nat_dec_le(v___x_1699_, v___x_1699_);
                    if v___x_1705_ == 0 {
                        if v___x_1701_ == 0 {
                            leanh::lean_dec(v_a_1694_);
                            if v_isShared_1697_ == 0 {
                                leanh::lean_ctor_set(v___x_1696_, 0, v___x_1700_);
                                v___x_1707_ = v___x_1696_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1708_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1700_);
                                v___x_1707_ = v_reuseFailAlloc_1708_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1696_);
                            v___x_1709_ = 0usize;
                            v___x_1710_ = lean_usize_of_nat(v___x_1699_);
                            v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_1694_, v___x_1709_, v___x_1710_, v___x_1700_, v___y_1690_, v___y_1691_);
                            leanh::lean_dec(v_a_1694_);
                            return v___x_1711_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1696_);
                        v___x_1712_ = 0usize;
                        v___x_1713_ = lean_usize_of_nat(v___x_1699_);
                        v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance_spec__0(v_a_1694_, v___x_1712_, v___x_1713_, v___x_1700_, v___y_1690_, v___y_1691_);
                        leanh::lean_dec(v_a_1694_);
                        return v___x_1714_;
                    }
                }
            }
            2 => {
                return v___x_1703_;
            }
            3 => {
                return v___x_1707_;
            }
            4 => {
                if v_isShared_1719_ == 0 {
                    v___x_1721_ = v___x_1718_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed(
    mut v___x_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0(v___x_1724_, v___y_1725_, v___y_1726_);
    leanh::lean_dec(v___y_1726_);
    leanh::lean_dec_ref(v___y_1725_);
    return v_res_1728_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(
    mut v_declName_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_1729_);
    v___x_1733_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___boxed as *mut core::ffi::c_void, 8, 1);
    leanh::lean_closure_set(v___x_1733_, 0, v_declName_1729_);
    v___f_1734_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_1734_, 0, v___x_1733_);
    v___x_1735_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_declName_1729_,
        v___f_1734_,
        v_a_1730_,
        v_a_1731_,
    );
    return v___x_1735_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance___boxed(
    mut v_declName_1736_: *mut leanh::LeanObject,
    mut v_a_1737_: *mut leanh::LeanObject,
    mut v_a_1738_: *mut leanh::LeanObject,
    mut v_a_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1740_ =
        l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(
            v_declName_1736_,
            v_a_1737_,
            v_a_1738_,
        );
    leanh::lean_dec(v_a_1738_);
    leanh::lean_dec_ref(v_a_1737_);
    return v_res_1740_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(
    mut v_declName_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = lean_st_ref_get(v___y_1742_);
    v_env_1745_ = leanh::lean_ctor_get(v___x_1744_, 0);
    leanh::lean_inc_ref(v_env_1745_);
    leanh::lean_dec(v___x_1744_);
    v___x_1746_ = l_Lean_isInductiveCore(v_env_1745_, v_declName_1741_);
    v___x_1747_ = leanh::lean_box((v___x_1746_) as usize);
    v___x_1748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1748_, 0, v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg___boxed(
    mut v_declName_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1752_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_1749_, v___y_1750_);
    leanh::lean_dec(v___y_1750_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(
    mut v_declName_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v_declName_1753_, v___y_1755_);
    return v___x_1757_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___boxed(
    mut v_declName_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1(v_declName_1758_, v___y_1759_, v___y_1760_);
    leanh::lean_dec(v___y_1760_);
    leanh::lean_dec_ref(v___y_1759_);
    return v_res_1762_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(
    mut v_____do__lift_1763_: u8,
    mut v___y_1764_: *mut leanh::LeanObject,
    mut v___y_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_1763_ == 0 {
        let mut v___x_1767_: u8 = 0;
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1767_ = 1;
        v___x_1768_ = leanh::lean_box((v___x_1767_) as usize);
        v___x_1769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
        return v___x_1769_;
    } else {
        let mut v___x_1770_: u8 = 0;
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1770_ = 0;
        v___x_1771_ = leanh::lean_box((v___x_1770_) as usize);
        v___x_1772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
        return v___x_1772_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0___boxed(
    mut v_____do__lift_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
    mut v___y_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_1736__boxed_1777_: u8 = 0;
    let mut v_res_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1736__boxed_1777_ = (leanh::lean_unbox(v_____do__lift_1773_) as u8);
    v_res_1778_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v_____do__lift_1736__boxed_1777_, v___y_1774_, v___y_1775_);
    leanh::lean_dec(v___y_1775_);
    leanh::lean_dec_ref(v___y_1774_);
    return v_res_1778_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(
    mut v_as_1779_: *mut leanh::LeanObject,
    mut v_i_1780_: usize,
    mut v_stop_1781_: usize,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v_a_1788_: u8 = 0;
    let mut v___x_1789_: usize = 0;
    let mut v___x_1790_: usize = 0;
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1799_: u8 = 0;
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1805_: u8 = 0;
    let mut v_a_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: u8 = 0;
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1785_ = lean_usize_dec_eq(v_i_1780_, v_stop_1781_);
                if v___x_1785_ == 0 {
                    v___x_1786_ = 1;
                    v___x_1794_ = lean_array_uget_borrowed(v_as_1779_, v_i_1780_);
                    leanh::lean_inc(v___x_1794_);
                    v___x_1795_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__1___redArg(v___x_1794_, v___y_1783_);
                    if leanh::lean_obj_tag(v___x_1795_) == 0 {
                        v_a_1796_ = leanh::lean_ctor_get(v___x_1795_, 0);
                        v_isSharedCheck_1805_ =
                            (!leanh::lean_is_exclusive(v___x_1795_)) as u8;
                        if v_isSharedCheck_1805_ == 0 {
                            v___x_1798_ = v___x_1795_;
                            v_isShared_1799_ = v_isSharedCheck_1805_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1796_);
                            leanh::lean_dec(v___x_1795_);
                            v___x_1798_ = leanh::lean_box(0);
                            v_isShared_1799_ = v_isSharedCheck_1805_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1795_) == 0 {
                            v_a_1806_ = leanh::lean_ctor_get(v___x_1795_, 0);
                            leanh::lean_inc(v_a_1806_);
                            leanh::lean_dec_ref_known(v___x_1795_, 1);
                            v___x_1807_ = (leanh::lean_unbox(v_a_1806_) as u8);
                            leanh::lean_dec(v_a_1806_);
                            v_a_1788_ = v___x_1807_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_1795_;
                        }
                    }
                } else {
                    v___x_1808_ = 0;
                    v___x_1809_ = leanh::lean_box((v___x_1808_) as usize);
                    v___x_1810_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1810_, 0, v___x_1809_);
                    return v___x_1810_;
                }
            }
            1 => {
                if v_a_1788_ == 0 {
                    v___x_1789_ = 1usize;
                    v___x_1790_ = lean_usize_add(v_i_1780_, v___x_1789_);
                    v_i_1780_ = v___x_1790_;
                    state = 0;
                    continue;
                } else {
                    v___x_1792_ = leanh::lean_box((v___x_1786_) as usize);
                    v___x_1793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                    return v___x_1793_;
                }
            }
            2 => {
                v___x_1800_ = (leanh::lean_unbox(v_a_1796_) as u8);
                leanh::lean_dec(v_a_1796_);
                if v___x_1800_ == 0 {
                    v___x_1801_ = leanh::lean_box((v___x_1786_) as usize);
                    if v_isShared_1799_ == 0 {
                        leanh::lean_ctor_set(v___x_1798_, 0, v___x_1801_);
                        v___x_1803_ = v___x_1798_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
                        v___x_1803_ = v_reuseFailAlloc_1804_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1798_);
                    v_a_1788_ = v___x_1785_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_1803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2___boxed(
    mut v_as_1811_: *mut leanh::LeanObject,
    mut v_i_1812_: *mut leanh::LeanObject,
    mut v_stop_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1817_: usize = 0;
    let mut v_stop_boxed_1818_: usize = 0;
    let mut v_res_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1817_ = leanh::lean_unbox_usize(v_i_1812_);
    leanh::lean_dec(v_i_1812_);
    v_stop_boxed_1818_ = leanh::lean_unbox_usize(v_stop_1813_);
    leanh::lean_dec(v_stop_1813_);
    v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_as_1811_, v_i_boxed_1817_, v_stop_boxed_1818_, v___y_1814_, v___y_1815_);
    leanh::lean_dec(v___y_1815_);
    leanh::lean_dec_ref(v___y_1814_);
    leanh::lean_dec_ref(v_as_1811_);
    return v_res_1819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(
    mut v_as_1820_: *mut leanh::LeanObject,
    mut v_sz_1821_: usize,
    mut v_i_1822_: usize,
    mut v_b_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: usize = 0;
    let mut v___x_1833_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1827_ = lean_usize_dec_lt(v_i_1822_, v_sz_1821_);
                if v___x_1827_ == 0 {
                    v___x_1828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1828_, 0, v_b_1823_);
                    return v___x_1828_;
                } else {
                    v_a_1829_ = lean_array_uget_borrowed(v_as_1820_, v_i_1822_);
                    leanh::lean_inc(v_a_1829_);
                    v___x_1830_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstance(v_a_1829_, v___y_1824_, v___y_1825_);
                    if leanh::lean_obj_tag(v___x_1830_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1830_, 1);
                        v___x_1831_ = leanh::lean_box(0);
                        v___x_1832_ = 1usize;
                        v___x_1833_ = lean_usize_add(v_i_1822_, v___x_1832_);
                        v_i_1822_ = v___x_1833_;
                        v_b_1823_ = v___x_1831_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1830_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0___boxed(
    mut v_as_1835_: *mut leanh::LeanObject,
    mut v_sz_1836_: *mut leanh::LeanObject,
    mut v_i_1837_: *mut leanh::LeanObject,
    mut v_b_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1842_: usize = 0;
    let mut v_i_boxed_1843_: usize = 0;
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1842_ = leanh::lean_unbox_usize(v_sz_1836_);
    leanh::lean_dec(v_sz_1836_);
    v_i_boxed_1843_ = leanh::lean_unbox_usize(v_i_1837_);
    leanh::lean_dec(v_i_1837_);
    v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_as_1835_, v_sz_boxed_1842_, v_i_boxed_1843_, v_b_1838_, v___y_1839_, v___y_1840_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    leanh::lean_dec_ref(v_as_1835_);
    return v_res_1844_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(
    mut v_declNames_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
    mut v_a_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_unused_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v___y_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: usize = 0;
    let mut v___x_1881_: usize = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1876_ = leanh::lean_unsigned_to_nat(0);
                v___x_1877_ = lean_array_get_size(v_declNames_1845_);
                v___x_1878_ = lean_nat_dec_lt(v___x_1876_, v___x_1877_);
                if v___x_1878_ == 0 {
                    v___x_1879_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_1878_, v_a_1846_, v_a_1847_);
                    v___y_1873_ = v___x_1879_;
                    state = 6;
                    continue;
                } else {
                    if v___x_1878_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1880_ = 0usize;
                        v___x_1881_ = lean_usize_of_nat(v___x_1877_);
                        v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__2(v_declNames_1845_, v___x_1880_, v___x_1881_, v_a_1846_, v_a_1847_);
                        if leanh::lean_obj_tag(v___x_1882_) == 0 {
                            v_a_1883_ = leanh::lean_ctor_get(v___x_1882_, 0);
                            leanh::lean_inc(v_a_1883_);
                            leanh::lean_dec_ref_known(v___x_1882_, 1);
                            v___x_1884_ = (leanh::lean_unbox(v_a_1883_) as u8);
                            leanh::lean_dec(v_a_1883_);
                            v___x_1885_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___lam__0(v___x_1884_, v_a_1846_, v_a_1847_);
                            v___y_1873_ = v___x_1885_;
                            state = 6;
                            continue;
                        } else {
                            v___y_1873_ = v___x_1882_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1850_ = leanh::lean_box(0);
                v_sz_1851_ = lean_array_size(v_declNames_1845_);
                v___x_1852_ = 0usize;
                v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler_spec__0(v_declNames_1845_, v_sz_1851_, v___x_1852_, v___x_1850_, v_a_1846_, v_a_1847_);
                if leanh::lean_obj_tag(v___x_1853_) == 0 {
                    v_isSharedCheck_1862_ = (!leanh::lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1862_ == 0 {
                        v_unused_1863_ = leanh::lean_ctor_get(v___x_1853_, 0);
                        leanh::lean_dec(v_unused_1863_);
                        v___x_1855_ = v___x_1853_;
                        v_isShared_1856_ = v_isSharedCheck_1862_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1853_);
                        v___x_1855_ = leanh::lean_box(0);
                        v_isShared_1856_ = v_isSharedCheck_1862_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1864_ = leanh::lean_ctor_get(v___x_1853_, 0);
                    v_isSharedCheck_1871_ = (!leanh::lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v___x_1866_ = v___x_1853_;
                        v_isShared_1867_ = v_isSharedCheck_1871_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1864_);
                        leanh::lean_dec(v___x_1853_);
                        v___x_1866_ = leanh::lean_box(0);
                        v_isShared_1867_ = v_isSharedCheck_1871_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1857_ = 1;
                v___x_1858_ = leanh::lean_box((v___x_1857_) as usize);
                if v_isShared_1856_ == 0 {
                    leanh::lean_ctor_set(v___x_1855_, 0, v___x_1858_);
                    v___x_1860_ = v___x_1855_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1860_;
            }
            4 => {
                if v_isShared_1867_ == 0 {
                    v___x_1869_ = v___x_1866_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
                    v___x_1869_ = v_reuseFailAlloc_1870_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1869_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_1873_) == 0 {
                    v_a_1874_ = leanh::lean_ctor_get(v___y_1873_, 0);
                    v___x_1875_ = (leanh::lean_unbox(v_a_1874_) as u8);
                    if v___x_1875_ == 0 {
                        return v___y_1873_;
                    } else {
                        leanh::lean_dec_ref_known(v___y_1873_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1873_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler___boxed(
    mut v_declNames_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1890_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceHandler(v_declNames_1886_, v_a_1887_, v_a_1888_);
    leanh::lean_dec(v_a_1888_);
    leanh::lean_dec_ref(v_a_1887_);
    leanh::lean_dec_ref(v_declNames_1886_);
    return v_res_1890_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__3;
    v___x_1959_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_;
    v___x_1960_ = l_Lean_Elab_registerDerivingHandler(v___x_1958_, v___x_1959_);
    if leanh::lean_obj_tag(v___x_1960_) == 0 {
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: u8 = 0;
        let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1960_, 1);
        v___x_1961_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_mkReflBEqInstanceCmds___closed__59;
        v___x_1962_ = 0;
        v___x_1963_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_;
        v___x_1964_ = l_Lean_registerTraceClass(v___x_1961_, v___x_1962_, v___x_1963_);
        return v___x_1964_;
    } else {
        return v___x_1960_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2____boxed(
    mut v_a_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
    return v_res_1966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_ReflBEq(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_ReflBEq_0__Lean_Elab_Deriving_ReflBEq_initFn_00___x40_Lean_Elab_Deriving_ReflBEq_333339820____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_ReflBEq(
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
pub unsafe fn initialize_Lean_Elab_Deriving_ReflBEq(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_ReflBEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_ReflBEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_ReflBEq(builtin);
}