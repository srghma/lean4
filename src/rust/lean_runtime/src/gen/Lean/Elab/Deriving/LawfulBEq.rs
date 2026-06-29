// Lean compiler output
// Module: Lean.Elab.Deriving.LawfulBEq
// Imports: Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util Init.LawfulBEqTactics
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_mkCIdent;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_List_lengthTR___redArg, l_String_toRawSubstring_x27,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__0_value) as *mut crate::leanh::LeanObject,16093780639914376387 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [76, 97, 119, 102, 117, 108, 66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,4990346031453733830 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__7_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__10_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__13_value) as *mut crate::leanh::LeanObject,8497769072906204829 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__15_value) as *mut crate::leanh::LeanObject,14557702332550915328 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18_value) as *mut crate::leanh::LeanObject,11064845058293668901 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__20_value) as *mut crate::leanh::LeanObject,7983999284776576032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 83, 105, 103, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__22_value) as *mut crate::leanh::LeanObject,5940551064397964566 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__24_value) as *mut crate::leanh::LeanObject,4498178684837002829 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__12_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__27_value) as *mut crate::leanh::LeanObject,13585030837571646948 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [76, 97, 119, 102, 117, 108, 66, 69, 113, 46, 109, 107, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,4990346031453733830 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__32_value) as *mut crate::leanh::LeanObject,11665138051623152438 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__34_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__36_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__38_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__41_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject,15755466758005450470 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,4735460618040695023 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__46_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__49_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [84, 83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 111, 109, 112, 97, 116, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__51_value) as *mut crate::leanh::LeanObject,432428189503149776 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__52_value) as *mut crate::leanh::LeanObject,6219319768759699177 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__53_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__55_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__56_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__58_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__59_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__57_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__60_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__54_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__61_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__50_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__62_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__47_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__63_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 121, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__65_value) as *mut crate::leanh::LeanObject,16173796135615239867 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [98, 121, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__68_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__48_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__70_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [116, 97, 99, 116, 105, 99, 68, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__72_value) as *mut crate::leanh::LeanObject,12369115935240678623 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [100, 101, 114, 105, 118, 105, 110, 103, 95, 76, 97, 119, 102, 117, 108, 69, 113, 95, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 102, 102, 105, 120, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__76_value) as *mut crate::leanh::LeanObject,7625897890118033792 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__77_value) as *mut crate::leanh::LeanObject,8715860392475343861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 97, 119, 102, 117, 108, 66, 69, 113, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject,3113176348997436611 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__79_value) as *mut crate::leanh::LeanObject,13671930204602339433 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__81_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 32, 96, 76, 97, 119, 102, 117, 108, 66, 69, 113, 96, 32, 102, 111, 114, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 115, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [68, 101, 114, 105, 118, 105, 110, 103, 32, 96, 76, 97, 119, 102, 117, 108, 66, 69, 113, 96, 32, 102, 111, 114, 32, 109, 117, 116, 117, 97, 108, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 115, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__1_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__2_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__3_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__4_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject,5241190260012038858 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__5_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,11780360243015552331 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__6_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13448030473979740982 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__7_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,16994396132711329375 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__8_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject,14600716118415331265 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__9_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject,17337541630859628119 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__10_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,18138568551262397930 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__11_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__12_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,946469573816870447 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__13_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__14_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18388005901855717914 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__15_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__4_value) as *mut crate::leanh::LeanObject,1163035212465189307 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__16_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__44_value) as *mut crate::leanh::LeanObject,6975094092015821581 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__17_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__45_value) as *mut crate::leanh::LeanObject,13277581588480117699 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__18_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__2_value) as *mut crate::leanh::LeanObject,4152206391749653006 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(
    mut v_a_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1047_: u8 = 0;
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1040_) == 0 {
                    v___x_1042_ = l_List_reverse___redArg(v_a_1041_);
                    return v___x_1042_;
                } else {
                    v_head_1043_ = crate::leanh::lean_ctor_get(v_a_1040_, 0);
                    v_tail_1044_ = crate::leanh::lean_ctor_get(v_a_1040_, 1);
                    v_isSharedCheck_1053_ = (!crate::leanh::lean_is_exclusive(v_a_1040_)) as u8;
                    if v_isSharedCheck_1053_ == 0 {
                        v___x_1046_ = v_a_1040_;
                        v_isShared_1047_ = v_isSharedCheck_1053_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1044_);
                        crate::leanh::lean_inc(v_head_1043_);
                        crate::leanh::lean_dec(v_a_1040_);
                        v___x_1046_ = crate::leanh::lean_box(0);
                        v_isShared_1047_ = v_isSharedCheck_1053_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1048_ = l_Lean_MessageData_ofSyntax(v_head_1043_);
                if v_isShared_1047_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1046_, 1, v_a_1041_);
                    crate::leanh::lean_ctor_set(v___x_1046_, 0, v___x_1048_);
                    v___x_1050_ = v___x_1046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_a_1041_);
                    v___x_1050_ = v_reuseFailAlloc_1052_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1040_ = v_tail_1044_;
                v_a_1041_ = v___x_1050_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(
    mut v_opts_1054_: *mut crate::leanh::LeanObject,
    mut v_opt_1055_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1056_ = crate::leanh::lean_ctor_get(v_opt_1055_, 0);
    v_defValue_1057_ = crate::leanh::lean_ctor_get(v_opt_1055_, 1);
    v_map_1058_ = crate::leanh::lean_ctor_get(v_opts_1054_, 0);
    v___x_1059_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1058_,
            v_name_1056_,
        );
    if crate::leanh::lean_obj_tag(v___x_1059_) == 0 {
        let mut v___x_1060_: u8 = 0;
        v___x_1060_ = (crate::leanh::lean_unbox(v_defValue_1057_) as u8);
        return v___x_1060_;
    } else {
        let mut v_val_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1061_ = crate::leanh::lean_ctor_get(v___x_1059_, 0);
        crate::leanh::lean_inc(v_val_1061_);
        crate::leanh::lean_dec_ref_known(v___x_1059_, 1);
        if crate::leanh::lean_obj_tag(v_val_1061_) == 1 {
            let mut v_v_1062_: u8 = 0;
            v_v_1062_ = crate::leanh::lean_ctor_get_uint8(v_val_1061_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1061_, 0);
            return v_v_1062_;
        } else {
            let mut v___x_1063_: u8 = 0;
            crate::leanh::lean_dec(v_val_1061_);
            v___x_1063_ = (crate::leanh::lean_unbox(v_defValue_1057_) as u8);
            return v___x_1063_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5___boxed(
    mut v_opts_1064_: *mut crate::leanh::LeanObject,
    mut v_opt_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1066_: u8 = 0;
    let mut v_r_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_opts_1064_, v_opt_1065_);
    crate::leanh::lean_dec_ref(v_opt_1065_);
    crate::leanh::lean_dec_ref(v_opts_1064_);
    v_r_1067_ = crate::leanh::lean_box((v_res_1066_) as usize);
    return v_r_1067_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = crate::leanh::lean_box(1);
    v___x_1069_ = l_Lean_MessageData_ofFormat(v___x_1068_);
    return v___x_1069_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__2;
    v___x_1074_ = l_Lean_MessageData_ofFormat(v___x_1073_);
    return v___x_1074_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(
    mut v_x_1075_: *mut crate::leanh::LeanObject,
    mut v_x_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v_before_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_unused_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1076_) == 0 {
                    return v_x_1075_;
                } else {
                    v_head_1077_ = crate::leanh::lean_ctor_get(v_x_1076_, 0);
                    v_tail_1078_ = crate::leanh::lean_ctor_get(v_x_1076_, 1);
                    v_isSharedCheck_1100_ = (!crate::leanh::lean_is_exclusive(v_x_1076_)) as u8;
                    if v_isSharedCheck_1100_ == 0 {
                        v___x_1080_ = v_x_1076_;
                        v_isShared_1081_ = v_isSharedCheck_1100_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1078_);
                        crate::leanh::lean_inc(v_head_1077_);
                        crate::leanh::lean_dec(v_x_1076_);
                        v___x_1080_ = crate::leanh::lean_box(0);
                        v_isShared_1081_ = v_isSharedCheck_1100_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1082_ = crate::leanh::lean_ctor_get(v_head_1077_, 0);
                v_isSharedCheck_1098_ = (!crate::leanh::lean_is_exclusive(v_head_1077_)) as u8;
                if v_isSharedCheck_1098_ == 0 {
                    v_unused_1099_ = crate::leanh::lean_ctor_get(v_head_1077_, 1);
                    crate::leanh::lean_dec(v_unused_1099_);
                    v___x_1084_ = v_head_1077_;
                    v_isShared_1085_ = v_isSharedCheck_1098_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1082_);
                    crate::leanh::lean_dec(v_head_1077_);
                    v___x_1084_ = crate::leanh::lean_box(0);
                    v_isShared_1085_ = v_isSharedCheck_1098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
                if v_isShared_1085_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1084_, 7);
                    crate::leanh::lean_ctor_set(v___x_1084_, 1, v___x_1086_);
                    crate::leanh::lean_ctor_set(v___x_1084_, 0, v_x_1075_);
                    v___x_1088_ = v___x_1084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_x_1075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 1, v___x_1086_);
                    v___x_1088_ = v_reuseFailAlloc_1097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__3);
                if v_isShared_1081_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1080_, 7);
                    crate::leanh::lean_ctor_set(v___x_1080_, 1, v___x_1089_);
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v___x_1088_);
                    v___x_1091_ = v___x_1080_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1089_);
                    v___x_1091_ = v_reuseFailAlloc_1096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1092_ = l_Lean_MessageData_ofSyntax(v_before_1082_);
                v___x_1093_ = l_Lean_indentD(v___x_1092_);
                v___x_1094_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1094_, 0, v___x_1091_);
                crate::leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
                v_x_1075_ = v___x_1094_;
                v_x_1076_ = v_tail_1078_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__1;
    v___x_1105_ = l_Lean_MessageData_ofFormat(v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(
    mut v_msgData_1106_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1107_: *mut crate::leanh::LeanObject,
    mut v___y_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: u8 = 0;
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1131_: u8 = 0;
    let mut v_unused_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1110_ = crate::leanh::lean_ctor_get(v___y_1108_, 2);
                v___x_1111_ = l_Lean_Elab_pp_macroStack;
                v___x_1112_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__5(v_options_1110_, v___x_1111_);
                if v___x_1112_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1107_);
                    v___x_1113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1113_, 0, v_msgData_1106_);
                    return v___x_1113_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1107_) == 0 {
                        v___x_1114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1114_, 0, v_msgData_1106_);
                        return v___x_1114_;
                    } else {
                        v_head_1115_ = crate::leanh::lean_ctor_get(v_macroStack_1107_, 0);
                        crate::leanh::lean_inc(v_head_1115_);
                        v_after_1116_ = crate::leanh::lean_ctor_get(v_head_1115_, 1);
                        v_isSharedCheck_1131_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1115_)) as u8;
                        if v_isSharedCheck_1131_ == 0 {
                            v_unused_1132_ = crate::leanh::lean_ctor_get(v_head_1115_, 0);
                            crate::leanh::lean_dec(v_unused_1132_);
                            v___x_1118_ = v_head_1115_;
                            v_isShared_1119_ = v_isSharedCheck_1131_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1116_);
                            crate::leanh::lean_dec(v_head_1115_);
                            v___x_1118_ = crate::leanh::lean_box(0);
                            v_isShared_1119_ = v_isSharedCheck_1131_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1120_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6___closed__0);
                if v_isShared_1119_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1118_, 7);
                    crate::leanh::lean_ctor_set(v___x_1118_, 1, v___x_1120_);
                    crate::leanh::lean_ctor_set(v___x_1118_, 0, v_msgData_1106_);
                    v___x_1122_ = v___x_1118_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1130_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_msgData_1106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1130_, 1, v___x_1120_);
                    v___x_1122_ = v_reuseFailAlloc_1130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1123_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___closed__2);
                v___x_1124_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1124_, 0, v___x_1122_);
                crate::leanh::lean_ctor_set(v___x_1124_, 1, v___x_1123_);
                v___x_1125_ = l_Lean_MessageData_ofSyntax(v_after_1116_);
                v___x_1126_ = l_Lean_indentD(v___x_1125_);
                v_msgData_1127_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1127_, 0, v___x_1124_);
                crate::leanh::lean_ctor_set(v_msgData_1127_, 1, v___x_1126_);
                v___x_1128_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4_spec__6(v_msgData_1127_, v_macroStack_1107_);
                v___x_1129_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1129_, 0, v___x_1128_);
                return v___x_1129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg___boxed(
    mut v_msgData_1133_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_1133_, v_macroStack_1134_, v___y_1135_);
    crate::leanh::lean_dec_ref(v___y_1135_);
    return v_res_1137_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(
    mut v_msgData_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = lean_st_ref_get(v___y_1142_);
    v_env_1145_ = crate::leanh::lean_ctor_get(v___x_1144_, 0);
    crate::leanh::lean_inc_ref(v_env_1145_);
    crate::leanh::lean_dec(v___x_1144_);
    v___x_1146_ = lean_st_ref_get(v___y_1140_);
    v_mctx_1147_ = crate::leanh::lean_ctor_get(v___x_1146_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1147_);
    crate::leanh::lean_dec(v___x_1146_);
    v_lctx_1148_ = crate::leanh::lean_ctor_get(v___y_1139_, 2);
    v_options_1149_ = crate::leanh::lean_ctor_get(v___y_1141_, 2);
    crate::leanh::lean_inc_ref(v_options_1149_);
    crate::leanh::lean_inc_ref(v_lctx_1148_);
    v___x_1150_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1150_, 0, v_env_1145_);
    crate::leanh::lean_ctor_set(v___x_1150_, 1, v_mctx_1147_);
    crate::leanh::lean_ctor_set(v___x_1150_, 2, v_lctx_1148_);
    crate::leanh::lean_ctor_set(v___x_1150_, 3, v_options_1149_);
    v___x_1151_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1151_, 0, v___x_1150_);
    crate::leanh::lean_ctor_set(v___x_1151_, 1, v_msgData_1138_);
    v___x_1152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2___boxed(
    mut v_msgData_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msgData_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
    crate::leanh::lean_dec(v___y_1157_);
    crate::leanh::lean_dec_ref(v___y_1156_);
    crate::leanh::lean_dec(v___y_1155_);
    crate::leanh::lean_dec_ref(v___y_1154_);
    return v_res_1159_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(
    mut v_msg_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
    mut v___y_1162_: *mut crate::leanh::LeanObject,
    mut v___y_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v___y_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1168_ = crate::leanh::lean_ctor_get(v___y_1165_, 5);
                v___x_1169_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_1160_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
                v_a_1170_ = crate::leanh::lean_ctor_get(v___x_1169_, 0);
                crate::leanh::lean_inc(v_a_1170_);
                crate::leanh::lean_dec_ref(v___x_1169_);
                v_macroStack_1171_ = crate::leanh::lean_ctor_get(v___y_1161_, 1);
                v___x_1172_ = l_Lean_Elab_getBetterRef(v_ref_1168_, v_macroStack_1171_);
                crate::leanh::lean_inc(v_macroStack_1171_);
                v___x_1173_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_a_1170_, v_macroStack_1171_, v___y_1165_);
                v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1173_, 0);
                v_isSharedCheck_1182_ = (!crate::leanh::lean_is_exclusive(v___x_1173_)) as u8;
                if v_isSharedCheck_1182_ == 0 {
                    v___x_1176_ = v___x_1173_;
                    v_isShared_1177_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1174_);
                    crate::leanh::lean_dec(v___x_1173_);
                    v___x_1176_ = crate::leanh::lean_box(0);
                    v_isShared_1177_ = v_isSharedCheck_1182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1172_);
                crate::leanh::lean_ctor_set(v___x_1178_, 1, v_a_1174_);
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1176_, 1);
                    crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1178_);
                    v___x_1180_ = v___x_1176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
                    v___x_1180_ = v_reuseFailAlloc_1181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg___boxed(
    mut v_msg_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
    mut v___y_1188_: *mut crate::leanh::LeanObject,
    mut v___y_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
    crate::leanh::lean_dec(v___y_1189_);
    crate::leanh::lean_dec_ref(v___y_1188_);
    crate::leanh::lean_dec(v___y_1187_);
    crate::leanh::lean_dec_ref(v___y_1186_);
    crate::leanh::lean_dec(v___y_1185_);
    crate::leanh::lean_dec_ref(v___y_1184_);
    return v_res_1191_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__0;
    v___x_1194_ = l_Lean_stringToMessageData(v___x_1193_);
    return v___x_1194_;
}
pub unsafe fn _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1196_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__2;
    v___x_1197_ = l_Lean_stringToMessageData(v___x_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(
    mut v_constName_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = lean_st_ref_get(v___y_1204_);
                v_env_1207_ = crate::leanh::lean_ctor_get(v___x_1206_, 0);
                crate::leanh::lean_inc_ref(v_env_1207_);
                crate::leanh::lean_dec(v___x_1206_);
                crate::leanh::lean_inc(v_constName_1198_);
                v___x_1208_ = l_Lean_isInductiveCore_x3f(v_env_1207_, v_constName_1198_);
                if crate::leanh::lean_obj_tag(v___x_1208_) == 0 {
                    v___x_1209_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__1);
                    v___x_1210_ = 0;
                    v___x_1211_ = l_Lean_MessageData_ofConstName(v_constName_1198_, v___x_1210_);
                    v___x_1212_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1209_);
                    crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
                    v___x_1213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3_once), _init_l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___closed__3);
                    v___x_1214_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1212_);
                    crate::leanh::lean_ctor_set(v___x_1214_, 1, v___x_1213_);
                    v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_1214_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
                    return v___x_1215_;
                } else {
                    crate::leanh::lean_dec(v_constName_1198_);
                    v_val_1216_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1223_ = (!crate::leanh::lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1223_ == 0 {
                        v___x_1218_ = v___x_1208_;
                        v_isShared_1219_ = v_isSharedCheck_1223_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1216_);
                        crate::leanh::lean_dec(v___x_1208_);
                        v___x_1218_ = crate::leanh::lean_box(0);
                        v_isShared_1219_ = v_isSharedCheck_1223_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1219_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1218_, 0);
                    v___x_1221_ = v___x_1218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_val_1216_);
                    v___x_1221_ = v_reuseFailAlloc_1222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0___boxed(
    mut v_constName_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec_ref(v___y_1229_);
    crate::leanh::lean_dec(v___y_1228_);
    crate::leanh::lean_dec_ref(v___y_1227_);
    crate::leanh::lean_dec(v___y_1226_);
    crate::leanh::lean_dec_ref(v___y_1225_);
    return v_res_1232_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: f64 = 0.0;
    v___x_1233_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1234_ = lean_float_of_nat(v___x_1233_);
    return v___x_1234_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(
    mut v_cls_1238_: *mut crate::leanh::LeanObject,
    mut v_msg_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v_tid_1264_: u64 = 0;
    let mut v_traces_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1268_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: f64 = 0.0;
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1245_ = crate::leanh::lean_ctor_get(v___y_1242_, 5);
                v___x_1246_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2_spec__2(v_msg_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
                v_a_1247_ = crate::leanh::lean_ctor_get(v___x_1246_, 0);
                v_isSharedCheck_1291_ = (!crate::leanh::lean_is_exclusive(v___x_1246_)) as u8;
                if v_isSharedCheck_1291_ == 0 {
                    v___x_1249_ = v___x_1246_;
                    v_isShared_1250_ = v_isSharedCheck_1291_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1247_);
                    crate::leanh::lean_dec(v___x_1246_);
                    v___x_1249_ = crate::leanh::lean_box(0);
                    v_isShared_1250_ = v_isSharedCheck_1291_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1251_ = lean_st_ref_take(v___y_1243_);
                v_traceState_1252_ = crate::leanh::lean_ctor_get(v___x_1251_, 4);
                v_env_1253_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                v_nextMacroScope_1254_ = crate::leanh::lean_ctor_get(v___x_1251_, 1);
                v_ngen_1255_ = crate::leanh::lean_ctor_get(v___x_1251_, 2);
                v_auxDeclNGen_1256_ = crate::leanh::lean_ctor_get(v___x_1251_, 3);
                v_cache_1257_ = crate::leanh::lean_ctor_get(v___x_1251_, 5);
                v_messages_1258_ = crate::leanh::lean_ctor_get(v___x_1251_, 6);
                v_infoState_1259_ = crate::leanh::lean_ctor_get(v___x_1251_, 7);
                v_snapshotTasks_1260_ = crate::leanh::lean_ctor_get(v___x_1251_, 8);
                v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v___x_1251_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1262_ = v___x_1251_;
                    v_isShared_1263_ = v_isSharedCheck_1290_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1260_);
                    crate::leanh::lean_inc(v_infoState_1259_);
                    crate::leanh::lean_inc(v_messages_1258_);
                    crate::leanh::lean_inc(v_cache_1257_);
                    crate::leanh::lean_inc(v_traceState_1252_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1256_);
                    crate::leanh::lean_inc(v_ngen_1255_);
                    crate::leanh::lean_inc(v_nextMacroScope_1254_);
                    crate::leanh::lean_inc(v_env_1253_);
                    crate::leanh::lean_dec(v___x_1251_);
                    v___x_1262_ = crate::leanh::lean_box(0);
                    v_isShared_1263_ = v_isSharedCheck_1290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1264_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1265_ = crate::leanh::lean_ctor_get(v_traceState_1252_, 0);
                v_isSharedCheck_1289_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1252_)) as u8;
                if v_isSharedCheck_1289_ == 0 {
                    v___x_1267_ = v_traceState_1252_;
                    v_isShared_1268_ = v_isSharedCheck_1289_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1265_);
                    crate::leanh::lean_dec(v_traceState_1252_);
                    v___x_1267_ = crate::leanh::lean_box(0);
                    v_isShared_1268_ = v_isSharedCheck_1289_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1269_ = crate::leanh::lean_box(0);
                v___x_1270_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__0);
                v___x_1271_ = 0;
                v___x_1272_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1;
                v___x_1273_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1273_, 0, v_cls_1238_);
                crate::leanh::lean_ctor_set(v___x_1273_, 1, v___x_1269_);
                crate::leanh::lean_ctor_set(v___x_1273_, 2, v___x_1272_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1270_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1270_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1273_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1271_,
                );
                v___x_1274_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__2;
                v___x_1275_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1273_);
                crate::leanh::lean_ctor_set(v___x_1275_, 1, v_a_1247_);
                crate::leanh::lean_ctor_set(v___x_1275_, 2, v___x_1274_);
                crate::leanh::lean_inc(v_ref_1245_);
                v___x_1276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1276_, 0, v_ref_1245_);
                crate::leanh::lean_ctor_set(v___x_1276_, 1, v___x_1275_);
                v___x_1277_ = l_Lean_PersistentArray_push___redArg(v_traces_1265_, v___x_1276_);
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1277_);
                    v___x_1279_ = v___x_1267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1288_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1277_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1288_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1264_,
                    );
                    v___x_1279_ = v_reuseFailAlloc_1288_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1262_, 4, v___x_1279_);
                    v___x_1281_ = v___x_1262_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1287_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_env_1253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_nextMacroScope_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_ngen_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_auxDeclNGen_1256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 4, v___x_1279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 5, v_cache_1257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 6, v_messages_1258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 7, v_infoState_1259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1287_, 8, v_snapshotTasks_1260_);
                    v___x_1281_ = v_reuseFailAlloc_1287_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1282_ = lean_st_ref_set(v___y_1243_, v___x_1281_);
                v___x_1283_ = crate::leanh::lean_box(0);
                if v_isShared_1250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1249_, 0, v___x_1283_);
                    v___x_1285_ = v___x_1249_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
                    v___x_1285_ = v_reuseFailAlloc_1286_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___boxed(
    mut v_cls_1292_: *mut crate::leanh::LeanObject,
    mut v_msg_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
    mut v___y_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_1292_, v_msg_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
    crate::leanh::lean_dec(v___y_1297_);
    crate::leanh::lean_dec_ref(v___y_1296_);
    crate::leanh::lean_dec(v___y_1295_);
    crate::leanh::lean_dec_ref(v___y_1294_);
    return v_res_1299_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3;
    v___x_1316_ = l_Lean_mkCIdent(v___x_1315_);
    return v___x_1316_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1333_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__30;
    v___x_1368_ = l_String_toRawSubstring_x27(v___x_1367_);
    return v___x_1368_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1395_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg___closed__1;
    v___x_1396_ = l_String_toRawSubstring_x27(v___x_1395_);
    return v___x_1396_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80;
    v___x_1488_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__82;
    v___x_1489_ = l_Lean_Name_append(v___x_1488_, v___x_1487_);
    return v___x_1489_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__84;
    v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__86;
    v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
    return v___x_1495_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__88;
    v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
    return v___x_1498_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(
    mut v_declName_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v_options_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1606_: u8 = 0;
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_a_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1646_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut v_a_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut v_a_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v___y_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_all_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1702_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1507_ = l_Lean_getConstInfoInduct___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__0(v_declName_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
                if crate::leanh::lean_obj_tag(v___x_1507_) == 0 {
                    v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                    crate::leanh::lean_inc(v_a_1508_);
                    crate::leanh::lean_dec_ref_known(v___x_1507_, 1);
                    v_all_1685_ = crate::leanh::lean_ctor_get(v_a_1508_, 3);
                    v___x_1686_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1687_ = l_List_lengthTR___redArg(v_all_1685_);
                    v___x_1688_ = lean_nat_dec_lt(v___x_1686_, v___x_1687_);
                    crate::leanh::lean_dec(v___x_1687_);
                    if v___x_1688_ == 0 {
                        v___y_1668_ = v_a_1500_;
                        v___y_1669_ = v_a_1501_;
                        v___y_1670_ = v_a_1502_;
                        v___y_1671_ = v_a_1503_;
                        v___y_1672_ = v_a_1504_;
                        v___y_1673_ = v_a_1505_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1508_);
                        v___x_1689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__89);
                        v___x_1690_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_1689_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
                        v_a_1691_ = crate::leanh::lean_ctor_get(v___x_1690_, 0);
                        v_isSharedCheck_1698_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1690_)) as u8;
                        if v_isSharedCheck_1698_ == 0 {
                            v___x_1693_ = v___x_1690_;
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1691_);
                            crate::leanh::lean_dec(v___x_1690_);
                            v___x_1693_ = crate::leanh::lean_box(0);
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                    v_isSharedCheck_1706_ = (!crate::leanh::lean_is_exclusive(v___x_1507_)) as u8;
                    if v_isSharedCheck_1706_ == 0 {
                        v___x_1701_ = v___x_1507_;
                        v_isShared_1702_ = v_isSharedCheck_1706_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1699_);
                        crate::leanh::lean_dec(v___x_1507_);
                        v___x_1701_ = crate::leanh::lean_box(0);
                        v_isShared_1702_ = v_isSharedCheck_1706_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1508_);
                v___x_1516_ = l_Lean_Elab_Deriving_mkInductArgNames(
                    v_a_1508_,
                    v___y_1510_,
                    v___y_1511_,
                    v___y_1512_,
                    v___y_1513_,
                    v___y_1514_,
                    v___y_1515_,
                );
                if crate::leanh::lean_obj_tag(v___x_1516_) == 0 {
                    v_a_1517_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                    crate::leanh::lean_inc_n(v_a_1517_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1516_, 1);
                    v___x_1518_ = l_Lean_Elab_Deriving_mkImplicitBinders(
                        v_a_1517_,
                        v___y_1510_,
                        v___y_1511_,
                        v___y_1512_,
                        v___y_1513_,
                        v___y_1514_,
                        v___y_1515_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1518_) == 0 {
                        v_a_1519_ = crate::leanh::lean_ctor_get(v___x_1518_, 0);
                        crate::leanh::lean_inc(v_a_1519_);
                        crate::leanh::lean_dec_ref_known(v___x_1518_, 1);
                        v___x_1520_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__1;
                        crate::leanh::lean_inc(v_a_1517_);
                        crate::leanh::lean_inc(v_a_1508_);
                        v___x_1521_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                            v___x_1520_,
                            v_a_1508_,
                            v_a_1517_,
                            v___y_1510_,
                            v___y_1511_,
                            v___y_1512_,
                            v___y_1513_,
                            v___y_1514_,
                            v___y_1515_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1521_) == 0 {
                            v_a_1522_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                            crate::leanh::lean_inc(v_a_1522_);
                            crate::leanh::lean_dec_ref_known(v___x_1521_, 1);
                            v___x_1523_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3;
                            crate::leanh::lean_inc(v_a_1517_);
                            crate::leanh::lean_inc(v_a_1508_);
                            v___x_1524_ = l_Lean_Elab_Deriving_mkInstImplicitBinders(
                                v___x_1523_,
                                v_a_1508_,
                                v_a_1517_,
                                v___y_1510_,
                                v___y_1511_,
                                v___y_1512_,
                                v___y_1513_,
                                v___y_1514_,
                                v___y_1515_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1524_) == 0 {
                                v_a_1525_ = crate::leanh::lean_ctor_get(v___x_1524_, 0);
                                crate::leanh::lean_inc(v_a_1525_);
                                crate::leanh::lean_dec_ref_known(v___x_1524_, 1);
                                v___x_1526_ = l_Lean_Elab_Deriving_mkInductiveApp___redArg(
                                    v_a_1508_,
                                    v_a_1517_,
                                    v___y_1514_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1526_) == 0 {
                                    v_a_1527_ = crate::leanh::lean_ctor_get(v___x_1526_, 0);
                                    v_isSharedCheck_1642_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1526_)) as u8;
                                    if v_isSharedCheck_1642_ == 0 {
                                        v___x_1529_ = v___x_1526_;
                                        v_isShared_1530_ = v_isSharedCheck_1642_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1527_);
                                        crate::leanh::lean_dec(v___x_1526_);
                                        v___x_1529_ = crate::leanh::lean_box(0);
                                        v_isShared_1530_ = v_isSharedCheck_1642_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1525_);
                                    crate::leanh::lean_dec(v_a_1522_);
                                    crate::leanh::lean_dec(v_a_1519_);
                                    v_a_1643_ = crate::leanh::lean_ctor_get(v___x_1526_, 0);
                                    v_isSharedCheck_1650_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1526_)) as u8;
                                    if v_isSharedCheck_1650_ == 0 {
                                        v___x_1645_ = v___x_1526_;
                                        v_isShared_1646_ = v_isSharedCheck_1650_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1643_);
                                        crate::leanh::lean_dec(v___x_1526_);
                                        v___x_1645_ = crate::leanh::lean_box(0);
                                        v_isShared_1646_ = v_isSharedCheck_1650_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1522_);
                                crate::leanh::lean_dec(v_a_1519_);
                                crate::leanh::lean_dec(v_a_1517_);
                                crate::leanh::lean_dec(v_a_1508_);
                                return v___x_1524_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1519_);
                            crate::leanh::lean_dec(v_a_1517_);
                            crate::leanh::lean_dec(v_a_1508_);
                            return v___x_1521_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1517_);
                        crate::leanh::lean_dec(v_a_1508_);
                        v_a_1651_ = crate::leanh::lean_ctor_get(v___x_1518_, 0);
                        v_isSharedCheck_1658_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1518_)) as u8;
                        if v_isSharedCheck_1658_ == 0 {
                            v___x_1653_ = v___x_1518_;
                            v_isShared_1654_ = v_isSharedCheck_1658_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1651_);
                            crate::leanh::lean_dec(v___x_1518_);
                            v___x_1653_ = crate::leanh::lean_box(0);
                            v_isShared_1654_ = v_isSharedCheck_1658_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1508_);
                    v_a_1659_ = crate::leanh::lean_ctor_get(v___x_1516_, 0);
                    v_isSharedCheck_1666_ = (!crate::leanh::lean_is_exclusive(v___x_1516_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1661_ = v___x_1516_;
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1659_);
                        crate::leanh::lean_dec(v___x_1516_);
                        v___x_1661_ = crate::leanh::lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_options_1531_ = crate::leanh::lean_ctor_get(v___y_1514_, 2);
                v_ref_1532_ = crate::leanh::lean_ctor_get(v___y_1514_, 5);
                v_quotContext_1533_ = crate::leanh::lean_ctor_get(v___y_1514_, 10);
                v_currMacroScope_1534_ = crate::leanh::lean_ctor_get(v___y_1514_, 11);
                v_inheritedTraceOptions_1535_ = crate::leanh::lean_ctor_get(v___y_1514_, 13);
                v___x_1536_ = l_Array_append___redArg(v_a_1519_, v_a_1522_);
                crate::leanh::lean_dec(v_a_1522_);
                v___x_1537_ = l_Array_append___redArg(v___x_1536_, v_a_1525_);
                crate::leanh::lean_dec(v_a_1525_);
                v___x_1538_ = 0;
                v___x_1539_ = l_Lean_SourceInfo_fromRef(v_ref_1532_, v___x_1538_);
                v___x_1540_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__8;
                v___x_1541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__9);
                v___x_1542_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__11;
                crate::leanh::lean_inc_n(v___x_1539_, 30);
                v___x_1543_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1542_, v_a_1527_);
                v___x_1544_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1540_, v___x_1541_, v___x_1543_);
                v___x_1545_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__14;
                v___x_1546_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__16;
                v___x_1547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__17);
                v___x_1548_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1548_, 1, v___x_1542_);
                crate::leanh::lean_ctor_set(v___x_1548_, 2, v___x_1547_);
                crate::leanh::lean_inc_ref_n(v___x_1548_, 12);
                v___x_1549_ = l_Lean_Syntax_node7(
                    v___x_1539_,
                    v___x_1546_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1548_,
                );
                v___x_1550_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__18;
                v___x_1551_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__19;
                v___x_1552_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__21;
                v___x_1553_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1552_, v___x_1548_);
                v___x_1554_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1554_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1554_, 1, v___x_1550_);
                v___x_1555_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__23;
                v___x_1556_ = l_Array_append___redArg(v___x_1547_, v___x_1537_);
                crate::leanh::lean_dec_ref(v___x_1537_);
                v___x_1557_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1542_);
                crate::leanh::lean_ctor_set(v___x_1557_, 2, v___x_1556_);
                v___x_1558_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__25;
                v___x_1559_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__26;
                v___x_1560_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1560_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1560_, 1, v___x_1559_);
                v___x_1561_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1558_, v___x_1560_, v___x_1544_);
                v___x_1562_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1555_, v___x_1557_, v___x_1561_);
                v___x_1563_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__28;
                v___x_1564_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__29;
                v___x_1565_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1565_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1565_, 1, v___x_1564_);
                v___x_1566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__31);
                v___x_1567_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__33;
                crate::leanh::lean_inc_n(v_currMacroScope_1534_, 2);
                crate::leanh::lean_inc_n(v_quotContext_1533_, 2);
                v___x_1568_ =
                    l_Lean_addMacroScope(v_quotContext_1533_, v___x_1567_, v_currMacroScope_1534_);
                v___x_1569_ = crate::leanh::lean_box(0);
                v___x_1570_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__35;
                v___x_1571_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1571_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1571_, 1, v___x_1566_);
                crate::leanh::lean_ctor_set(v___x_1571_, 2, v___x_1568_);
                crate::leanh::lean_ctor_set(v___x_1571_, 3, v___x_1570_);
                v___x_1572_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__37;
                v___x_1573_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__39;
                v___x_1574_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__40;
                v___x_1575_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1575_, 1, v___x_1574_);
                v___x_1576_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__42;
                v___x_1577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__43);
                v___x_1578_ = crate::leanh::lean_box(0);
                v___x_1579_ =
                    l_Lean_addMacroScope(v_quotContext_1533_, v___x_1578_, v_currMacroScope_1534_);
                v___x_1580_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__64;
                v___x_1581_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1581_, 1, v___x_1577_);
                crate::leanh::lean_ctor_set(v___x_1581_, 2, v___x_1579_);
                crate::leanh::lean_ctor_set(v___x_1581_, 3, v___x_1580_);
                v___x_1582_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1576_, v___x_1581_);
                v___x_1583_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1573_, v___x_1575_, v___x_1582_);
                v___x_1584_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__66;
                v___x_1585_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__67;
                v___x_1586_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
                v___x_1587_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__69;
                v___x_1588_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__71;
                v___x_1589_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__73;
                v___x_1590_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__74;
                v___x_1591_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1591_, 1, v___x_1590_);
                v___x_1592_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1589_, v___x_1591_);
                v___x_1593_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1542_, v___x_1592_);
                v___x_1594_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1588_, v___x_1593_);
                v___x_1595_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1587_, v___x_1594_);
                v___x_1596_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1584_, v___x_1586_, v___x_1595_);
                v___x_1597_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__75;
                v___x_1598_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1598_, 0, v___x_1539_);
                crate::leanh::lean_ctor_set(v___x_1598_, 1, v___x_1597_);
                v___x_1599_ = l_Lean_Syntax_node3(
                    v___x_1539_,
                    v___x_1572_,
                    v___x_1583_,
                    v___x_1596_,
                    v___x_1598_,
                );
                v___x_1600_ = l_Lean_Syntax_node1(v___x_1539_, v___x_1542_, v___x_1599_);
                v___x_1601_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1540_, v___x_1571_, v___x_1600_);
                v___x_1602_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__78;
                v___x_1603_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1602_, v___x_1548_, v___x_1548_);
                v___x_1604_ = l_Lean_Syntax_node4(
                    v___x_1539_,
                    v___x_1563_,
                    v___x_1565_,
                    v___x_1601_,
                    v___x_1603_,
                    v___x_1548_,
                );
                v___x_1605_ = l_Lean_Syntax_node6(
                    v___x_1539_,
                    v___x_1551_,
                    v___x_1553_,
                    v___x_1554_,
                    v___x_1548_,
                    v___x_1548_,
                    v___x_1562_,
                    v___x_1604_,
                );
                v_hasTrace_1606_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_1531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_1607_ =
                    l_Lean_Syntax_node2(v___x_1539_, v___x_1545_, v___x_1549_, v___x_1605_);
                v___x_1608_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
                v___x_1610_ = lean_array_push(v___x_1609_, v___x_1607_);
                if v_hasTrace_1606_ == 0 {
                    if v_isShared_1530_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1529_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1614_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80;
                    v___x_1615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__83);
                    v___x_1616_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1535_,
                        v_options_1531_,
                        v___x_1615_,
                    );
                    if v___x_1616_ == 0 {
                        if v_isShared_1530_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1610_);
                            v___x_1618_ = v___x_1529_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1619_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1610_);
                            v___x_1618_ = v_reuseFailAlloc_1619_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1529_);
                        v___x_1620_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__85);
                        crate::leanh::lean_inc_ref(v___x_1610_);
                        v___x_1621_ = lean_array_to_list(v___x_1610_);
                        v___x_1622_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__1(v___x_1621_, v___x_1569_);
                        v___x_1623_ = l_Lean_MessageData_ofList(v___x_1622_);
                        v___x_1624_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1620_);
                        crate::leanh::lean_ctor_set(v___x_1624_, 1, v___x_1623_);
                        v___x_1625_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v___x_1614_, v___x_1624_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
                        if crate::leanh::lean_obj_tag(v___x_1625_) == 0 {
                            v_isSharedCheck_1632_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1625_)) as u8;
                            if v_isSharedCheck_1632_ == 0 {
                                v_unused_1633_ = crate::leanh::lean_ctor_get(v___x_1625_, 0);
                                crate::leanh::lean_dec(v_unused_1633_);
                                v___x_1627_ = v___x_1625_;
                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1625_);
                                v___x_1627_ = crate::leanh::lean_box(0);
                                v_isShared_1628_ = v_isSharedCheck_1632_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1610_);
                            v_a_1634_ = crate::leanh::lean_ctor_get(v___x_1625_, 0);
                            v_isSharedCheck_1641_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1625_)) as u8;
                            if v_isSharedCheck_1641_ == 0 {
                                v___x_1636_ = v___x_1625_;
                                v_isShared_1637_ = v_isSharedCheck_1641_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1634_);
                                crate::leanh::lean_dec(v___x_1625_);
                                v___x_1636_ = crate::leanh::lean_box(0);
                                v_isShared_1637_ = v_isSharedCheck_1641_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_1612_;
            }
            4 => {
                return v___x_1618_;
            }
            5 => {
                if v_isShared_1628_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1627_, 0, v___x_1610_);
                    v___x_1630_ = v___x_1627_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1610_);
                    v___x_1630_ = v_reuseFailAlloc_1631_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1630_;
            }
            7 => {
                if v_isShared_1637_ == 0 {
                    v___x_1639_ = v___x_1636_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
                    v___x_1639_ = v_reuseFailAlloc_1640_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1639_;
            }
            9 => {
                if v_isShared_1646_ == 0 {
                    v___x_1648_ = v___x_1645_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
                    v___x_1648_ = v_reuseFailAlloc_1649_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1648_;
            }
            11 => {
                if v_isShared_1654_ == 0 {
                    v___x_1656_ = v___x_1653_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1656_;
            }
            13 => {
                if v_isShared_1662_ == 0 {
                    v___x_1664_ = v___x_1661_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
                    v___x_1664_ = v_reuseFailAlloc_1665_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1664_;
            }
            15 => {
                v___x_1674_ = l_Lean_InductiveVal_isNested(v_a_1508_);
                if v___x_1674_ == 0 {
                    v___y_1510_ = v___y_1668_;
                    v___y_1511_ = v___y_1669_;
                    v___y_1512_ = v___y_1670_;
                    v___y_1513_ = v___y_1671_;
                    v___y_1514_ = v___y_1672_;
                    v___y_1515_ = v___y_1673_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1508_);
                    v___x_1675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87_once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__87);
                    v___x_1676_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v___x_1675_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
                    v_a_1677_ = crate::leanh::lean_ctor_get(v___x_1676_, 0);
                    v_isSharedCheck_1684_ = (!crate::leanh::lean_is_exclusive(v___x_1676_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v___x_1679_ = v___x_1676_;
                        v_isShared_1680_ = v_isSharedCheck_1684_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1677_);
                        crate::leanh::lean_dec(v___x_1676_);
                        v___x_1679_ = crate::leanh::lean_box(0);
                        v_isShared_1680_ = v_isSharedCheck_1684_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_1680_ == 0 {
                    v___x_1682_ = v___x_1679_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
                    v___x_1682_ = v_reuseFailAlloc_1683_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1682_;
            }
            18 => {
                if v_isShared_1694_ == 0 {
                    v___x_1696_ = v___x_1693_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1697_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1696_;
            }
            20 => {
                if v_isShared_1702_ == 0 {
                    v___x_1704_ = v___x_1701_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
                    v___x_1704_ = v_reuseFailAlloc_1705_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed(
    mut v_declName_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
    mut v_a_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds(v_declName_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
    crate::leanh::lean_dec(v_a_1713_);
    crate::leanh::lean_dec_ref(v_a_1712_);
    crate::leanh::lean_dec(v_a_1711_);
    crate::leanh::lean_dec_ref(v_a_1710_);
    crate::leanh::lean_dec(v_a_1709_);
    crate::leanh::lean_dec_ref(v_a_1708_);
    return v_res_1715_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(
    mut v_cls_1716_: *mut crate::leanh::LeanObject,
    mut v_msg_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___redArg(v_cls_1716_, v_msg_1717_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
    return v___x_1725_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2___boxed(
    mut v_cls_1726_: *mut crate::leanh::LeanObject,
    mut v_msg_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1735_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__2(v_cls_1726_, v_msg_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
    crate::leanh::lean_dec(v___y_1733_);
    crate::leanh::lean_dec_ref(v___y_1732_);
    crate::leanh::lean_dec(v___y_1731_);
    crate::leanh::lean_dec_ref(v___y_1730_);
    crate::leanh::lean_dec(v___y_1729_);
    crate::leanh::lean_dec_ref(v___y_1728_);
    return v_res_1735_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(
    mut v_00_u03b1_1736_: *mut crate::leanh::LeanObject,
    mut v_msg_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
    mut v___y_1739_: *mut crate::leanh::LeanObject,
    mut v___y_1740_: *mut crate::leanh::LeanObject,
    mut v___y_1741_: *mut crate::leanh::LeanObject,
    mut v___y_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___redArg(v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
    return v___x_1745_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3___boxed(
    mut v_00_u03b1_1746_: *mut crate::leanh::LeanObject,
    mut v_msg_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3(v_00_u03b1_1746_, v_msg_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v___y_1752_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec_ref(v___y_1750_);
    crate::leanh::lean_dec(v___y_1749_);
    crate::leanh::lean_dec_ref(v___y_1748_);
    return v_res_1755_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(
    mut v_msgData_1756_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___redArg(v_msgData_1756_, v_macroStack_1757_, v___y_1762_);
    return v___x_1765_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4___boxed(
    mut v_msgData_1766_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1767_: *mut crate::leanh::LeanObject,
    mut v___y_1768_: *mut crate::leanh::LeanObject,
    mut v___y_1769_: *mut crate::leanh::LeanObject,
    mut v___y_1770_: *mut crate::leanh::LeanObject,
    mut v___y_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1775_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds_spec__3_spec__4(v_msgData_1766_, v_macroStack_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
    crate::leanh::lean_dec(v___y_1773_);
    crate::leanh::lean_dec_ref(v___y_1772_);
    crate::leanh::lean_dec(v___y_1771_);
    crate::leanh::lean_dec_ref(v___y_1770_);
    crate::leanh::lean_dec(v___y_1769_);
    crate::leanh::lean_dec_ref(v___y_1768_);
    return v_res_1775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(
    mut v_as_1776_: *mut crate::leanh::LeanObject,
    mut v_i_1777_: usize,
    mut v_stop_1778_: usize,
    mut v_b_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: usize = 0;
    let mut v___x_1788_: usize = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1783_ = lean_usize_dec_eq(v_i_1777_, v_stop_1778_);
                if v___x_1783_ == 0 {
                    v___x_1784_ = lean_array_uget_borrowed(v_as_1776_, v_i_1777_);
                    crate::leanh::lean_inc(v___x_1784_);
                    v___x_1785_ =
                        l_Lean_Elab_Command_elabCommand(v___x_1784_, v___y_1780_, v___y_1781_);
                    if crate::leanh::lean_obj_tag(v___x_1785_) == 0 {
                        v_a_1786_ = crate::leanh::lean_ctor_get(v___x_1785_, 0);
                        crate::leanh::lean_inc(v_a_1786_);
                        crate::leanh::lean_dec_ref_known(v___x_1785_, 1);
                        v___x_1787_ = 1usize;
                        v___x_1788_ = lean_usize_add(v_i_1777_, v___x_1787_);
                        v_i_1777_ = v___x_1788_;
                        v_b_1779_ = v_a_1786_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1785_;
                    }
                } else {
                    v___x_1790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1790_, 0, v_b_1779_);
                    return v___x_1790_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0___boxed(
    mut v_as_1791_: *mut crate::leanh::LeanObject,
    mut v_i_1792_: *mut crate::leanh::LeanObject,
    mut v_stop_1793_: *mut crate::leanh::LeanObject,
    mut v_b_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1798_: usize = 0;
    let mut v_stop_boxed_1799_: usize = 0;
    let mut v_res_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1798_ = crate::leanh::lean_unbox_usize(v_i_1792_);
    crate::leanh::lean_dec(v_i_1792_);
    v_stop_boxed_1799_ = crate::leanh::lean_unbox_usize(v_stop_1793_);
    crate::leanh::lean_dec(v_stop_1793_);
    v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_as_1791_, v_i_boxed_1798_, v_stop_boxed_1799_, v_b_1794_, v___y_1795_, v___y_1796_);
    crate::leanh::lean_dec(v___y_1796_);
    crate::leanh::lean_dec_ref(v___y_1795_);
    crate::leanh::lean_dec_ref(v_as_1791_);
    return v_res_1800_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(
    mut v___x_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: usize = 0;
    let mut v___x_1822_: usize = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1805_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                    v___x_1801_,
                    v___y_1802_,
                    v___y_1803_,
                );
                if crate::leanh::lean_obj_tag(v___x_1805_) == 0 {
                    v_a_1806_ = crate::leanh::lean_ctor_get(v___x_1805_, 0);
                    v_isSharedCheck_1827_ = (!crate::leanh::lean_is_exclusive(v___x_1805_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1808_ = v___x_1805_;
                        v_isShared_1809_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1806_);
                        crate::leanh::lean_dec(v___x_1805_);
                        v___x_1808_ = crate::leanh::lean_box(0);
                        v_isShared_1809_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1805_, 0);
                    v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v___x_1805_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1830_ = v___x_1805_;
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1828_);
                        crate::leanh::lean_dec(v___x_1805_);
                        v___x_1830_ = crate::leanh::lean_box(0);
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1810_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1811_ = lean_array_get_size(v_a_1806_);
                v___x_1812_ = crate::leanh::lean_box(0);
                v___x_1813_ = lean_nat_dec_lt(v___x_1810_, v___x_1811_);
                if v___x_1813_ == 0 {
                    crate::leanh::lean_dec(v_a_1806_);
                    if v_isShared_1809_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1812_);
                        v___x_1815_ = v___x_1808_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1812_);
                        v___x_1815_ = v_reuseFailAlloc_1816_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1817_ = lean_nat_dec_le(v___x_1811_, v___x_1811_);
                    if v___x_1817_ == 0 {
                        if v___x_1813_ == 0 {
                            crate::leanh::lean_dec(v_a_1806_);
                            if v_isShared_1809_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1812_);
                                v___x_1819_ = v___x_1808_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1820_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1812_);
                                v___x_1819_ = v_reuseFailAlloc_1820_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1808_);
                            v___x_1821_ = 0usize;
                            v___x_1822_ = lean_usize_of_nat(v___x_1811_);
                            v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_1806_, v___x_1821_, v___x_1822_, v___x_1812_, v___y_1802_, v___y_1803_);
                            crate::leanh::lean_dec(v_a_1806_);
                            return v___x_1823_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1808_);
                        v___x_1824_ = 0usize;
                        v___x_1825_ = lean_usize_of_nat(v___x_1811_);
                        v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance_spec__0(v_a_1806_, v___x_1824_, v___x_1825_, v___x_1812_, v___y_1802_, v___y_1803_);
                        crate::leanh::lean_dec(v_a_1806_);
                        return v___x_1826_;
                    }
                }
            }
            2 => {
                return v___x_1815_;
            }
            3 => {
                return v___x_1819_;
            }
            4 => {
                if v_isShared_1831_ == 0 {
                    v___x_1833_ = v___x_1830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed(
    mut v___x_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1840_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0(v___x_1836_, v___y_1837_, v___y_1838_);
    crate::leanh::lean_dec(v___y_1838_);
    crate::leanh::lean_dec_ref(v___y_1837_);
    return v_res_1840_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(
    mut v_declName_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_declName_1841_);
    v___x_1845_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___boxed as *mut core::ffi::c_void, 8, 1);
    crate::leanh::lean_closure_set(v___x_1845_, 0, v_declName_1841_);
    v___f_1846_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_1846_, 0, v___x_1845_);
    v___x_1847_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
        v_declName_1841_,
        v___f_1846_,
        v_a_1842_,
        v_a_1843_,
    );
    return v___x_1847_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance___boxed(
    mut v_declName_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1852_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_declName_1848_, v_a_1849_, v_a_1850_);
    crate::leanh::lean_dec(v_a_1850_);
    crate::leanh::lean_dec_ref(v_a_1849_);
    return v_res_1852_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(
    mut v_declName_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1856_ = lean_st_ref_get(v___y_1854_);
    v_env_1857_ = crate::leanh::lean_ctor_get(v___x_1856_, 0);
    crate::leanh::lean_inc_ref(v_env_1857_);
    crate::leanh::lean_dec(v___x_1856_);
    v___x_1858_ = l_Lean_isInductiveCore(v_env_1857_, v_declName_1853_);
    v___x_1859_ = crate::leanh::lean_box((v___x_1858_) as usize);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg___boxed(
    mut v_declName_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1864_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_1861_, v___y_1862_);
    crate::leanh::lean_dec(v___y_1862_);
    return v_res_1864_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(
    mut v_declName_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v_declName_1865_, v___y_1867_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___boxed(
    mut v_declName_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1(v_declName_1870_, v___y_1871_, v___y_1872_);
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    return v_res_1874_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(
    mut v_____do__lift_1875_: u8,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_1875_ == 0 {
        let mut v___x_1879_: u8 = 0;
        let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1879_ = 1;
        v___x_1880_ = crate::leanh::lean_box((v___x_1879_) as usize);
        v___x_1881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1881_, 0, v___x_1880_);
        return v___x_1881_;
    } else {
        let mut v___x_1882_: u8 = 0;
        let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1882_ = 0;
        v___x_1883_ = crate::leanh::lean_box((v___x_1882_) as usize);
        v___x_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1884_, 0, v___x_1883_);
        return v___x_1884_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0___boxed(
    mut v_____do__lift_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
    mut v___y_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_1736__boxed_1889_: u8 = 0;
    let mut v_res_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1736__boxed_1889_ = (crate::leanh::lean_unbox(v_____do__lift_1885_) as u8);
    v_res_1890_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v_____do__lift_1736__boxed_1889_, v___y_1886_, v___y_1887_);
    crate::leanh::lean_dec(v___y_1887_);
    crate::leanh::lean_dec_ref(v___y_1886_);
    return v_res_1890_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(
    mut v_as_1891_: *mut crate::leanh::LeanObject,
    mut v_i_1892_: usize,
    mut v_stop_1893_: usize,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: u8 = 0;
    let mut v_a_1900_: u8 = 0;
    let mut v___x_1901_: usize = 0;
    let mut v___x_1902_: usize = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1912_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1897_ = lean_usize_dec_eq(v_i_1892_, v_stop_1893_);
                if v___x_1897_ == 0 {
                    v___x_1898_ = 1;
                    v___x_1906_ = lean_array_uget_borrowed(v_as_1891_, v_i_1892_);
                    crate::leanh::lean_inc(v___x_1906_);
                    v___x_1907_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__1___redArg(v___x_1906_, v___y_1895_);
                    if crate::leanh::lean_obj_tag(v___x_1907_) == 0 {
                        v_a_1908_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                        v_isSharedCheck_1917_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1907_)) as u8;
                        if v_isSharedCheck_1917_ == 0 {
                            v___x_1910_ = v___x_1907_;
                            v_isShared_1911_ = v_isSharedCheck_1917_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1908_);
                            crate::leanh::lean_dec(v___x_1907_);
                            v___x_1910_ = crate::leanh::lean_box(0);
                            v_isShared_1911_ = v_isSharedCheck_1917_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1907_) == 0 {
                            v_a_1918_ = crate::leanh::lean_ctor_get(v___x_1907_, 0);
                            crate::leanh::lean_inc(v_a_1918_);
                            crate::leanh::lean_dec_ref_known(v___x_1907_, 1);
                            v___x_1919_ = (crate::leanh::lean_unbox(v_a_1918_) as u8);
                            crate::leanh::lean_dec(v_a_1918_);
                            v_a_1900_ = v___x_1919_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_1907_;
                        }
                    }
                } else {
                    v___x_1920_ = 0;
                    v___x_1921_ = crate::leanh::lean_box((v___x_1920_) as usize);
                    v___x_1922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1922_, 0, v___x_1921_);
                    return v___x_1922_;
                }
            }
            1 => {
                if v_a_1900_ == 0 {
                    v___x_1901_ = 1usize;
                    v___x_1902_ = lean_usize_add(v_i_1892_, v___x_1901_);
                    v_i_1892_ = v___x_1902_;
                    state = 0;
                    continue;
                } else {
                    v___x_1904_ = crate::leanh::lean_box((v___x_1898_) as usize);
                    v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                    return v___x_1905_;
                }
            }
            2 => {
                v___x_1912_ = (crate::leanh::lean_unbox(v_a_1908_) as u8);
                crate::leanh::lean_dec(v_a_1908_);
                if v___x_1912_ == 0 {
                    v___x_1913_ = crate::leanh::lean_box((v___x_1898_) as usize);
                    if v_isShared_1911_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1913_);
                        v___x_1915_ = v___x_1910_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
                        v___x_1915_ = v_reuseFailAlloc_1916_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1910_);
                    v_a_1900_ = v___x_1897_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_1915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2___boxed(
    mut v_as_1923_: *mut crate::leanh::LeanObject,
    mut v_i_1924_: *mut crate::leanh::LeanObject,
    mut v_stop_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1929_: usize = 0;
    let mut v_stop_boxed_1930_: usize = 0;
    let mut v_res_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1929_ = crate::leanh::lean_unbox_usize(v_i_1924_);
    crate::leanh::lean_dec(v_i_1924_);
    v_stop_boxed_1930_ = crate::leanh::lean_unbox_usize(v_stop_1925_);
    crate::leanh::lean_dec(v_stop_1925_);
    v_res_1931_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_as_1923_, v_i_boxed_1929_, v_stop_boxed_1930_, v___y_1926_, v___y_1927_);
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec_ref(v_as_1923_);
    return v_res_1931_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(
    mut v_as_1932_: *mut crate::leanh::LeanObject,
    mut v_sz_1933_: usize,
    mut v_i_1934_: usize,
    mut v_b_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1939_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
                if v___x_1939_ == 0 {
                    v___x_1940_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1940_, 0, v_b_1935_);
                    return v___x_1940_;
                } else {
                    v_a_1941_ = lean_array_uget_borrowed(v_as_1932_, v_i_1934_);
                    crate::leanh::lean_inc(v_a_1941_);
                    v___x_1942_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstance(v_a_1941_, v___y_1936_, v___y_1937_);
                    if crate::leanh::lean_obj_tag(v___x_1942_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1942_, 1);
                        v___x_1943_ = crate::leanh::lean_box(0);
                        v___x_1944_ = 1usize;
                        v___x_1945_ = lean_usize_add(v_i_1934_, v___x_1944_);
                        v_i_1934_ = v___x_1945_;
                        v_b_1935_ = v___x_1943_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1942_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0___boxed(
    mut v_as_1947_: *mut crate::leanh::LeanObject,
    mut v_sz_1948_: *mut crate::leanh::LeanObject,
    mut v_i_1949_: *mut crate::leanh::LeanObject,
    mut v_b_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1954_: usize = 0;
    let mut v_i_boxed_1955_: usize = 0;
    let mut v_res_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1954_ = crate::leanh::lean_unbox_usize(v_sz_1948_);
    crate::leanh::lean_dec(v_sz_1948_);
    v_i_boxed_1955_ = crate::leanh::lean_unbox_usize(v_i_1949_);
    crate::leanh::lean_dec(v_i_1949_);
    v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_as_1947_, v_sz_boxed_1954_, v_i_boxed_1955_, v_b_1950_, v___y_1951_, v___y_1952_);
    crate::leanh::lean_dec(v___y_1952_);
    crate::leanh::lean_dec_ref(v___y_1951_);
    crate::leanh::lean_dec_ref(v_as_1947_);
    return v_res_1956_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(
    mut v_declNames_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
    mut v_a_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1963_: usize = 0;
    let mut v___x_1964_: usize = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1974_: u8 = 0;
    let mut v_unused_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v___y_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: usize = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1988_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1989_ = lean_array_get_size(v_declNames_1957_);
                v___x_1990_ = lean_nat_dec_lt(v___x_1988_, v___x_1989_);
                if v___x_1990_ == 0 {
                    v___x_1991_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_1990_, v_a_1958_, v_a_1959_);
                    v___y_1985_ = v___x_1991_;
                    state = 6;
                    continue;
                } else {
                    if v___x_1990_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1992_ = 0usize;
                        v___x_1993_ = lean_usize_of_nat(v___x_1989_);
                        v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__2(v_declNames_1957_, v___x_1992_, v___x_1993_, v_a_1958_, v_a_1959_);
                        if crate::leanh::lean_obj_tag(v___x_1994_) == 0 {
                            v_a_1995_ = crate::leanh::lean_ctor_get(v___x_1994_, 0);
                            crate::leanh::lean_inc(v_a_1995_);
                            crate::leanh::lean_dec_ref_known(v___x_1994_, 1);
                            v___x_1996_ = (crate::leanh::lean_unbox(v_a_1995_) as u8);
                            crate::leanh::lean_dec(v_a_1995_);
                            v___x_1997_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___lam__0(v___x_1996_, v_a_1958_, v_a_1959_);
                            v___y_1985_ = v___x_1997_;
                            state = 6;
                            continue;
                        } else {
                            v___y_1985_ = v___x_1994_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1962_ = crate::leanh::lean_box(0);
                v_sz_1963_ = lean_array_size(v_declNames_1957_);
                v___x_1964_ = 0usize;
                v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler_spec__0(v_declNames_1957_, v_sz_1963_, v___x_1964_, v___x_1962_, v_a_1958_, v_a_1959_);
                if crate::leanh::lean_obj_tag(v___x_1965_) == 0 {
                    v_isSharedCheck_1974_ = (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                    if v_isSharedCheck_1974_ == 0 {
                        v_unused_1975_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                        crate::leanh::lean_dec(v_unused_1975_);
                        v___x_1967_ = v___x_1965_;
                        v_isShared_1968_ = v_isSharedCheck_1974_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1965_);
                        v___x_1967_ = crate::leanh::lean_box(0);
                        v_isShared_1968_ = v_isSharedCheck_1974_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1978_ = v___x_1965_;
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1976_);
                        crate::leanh::lean_dec(v___x_1965_);
                        v___x_1978_ = crate::leanh::lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1969_ = 1;
                v___x_1970_ = crate::leanh::lean_box((v___x_1969_) as usize);
                if v_isShared_1968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1967_, 0, v___x_1970_);
                    v___x_1972_ = v___x_1967_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
                    v___x_1972_ = v_reuseFailAlloc_1973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1972_;
            }
            4 => {
                if v_isShared_1979_ == 0 {
                    v___x_1981_ = v___x_1978_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1981_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_1985_) == 0 {
                    v_a_1986_ = crate::leanh::lean_ctor_get(v___y_1985_, 0);
                    v___x_1987_ = (crate::leanh::lean_unbox(v_a_1986_) as u8);
                    if v___x_1987_ == 0 {
                        return v___y_1985_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_1985_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1985_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler___boxed(
    mut v_declNames_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_a_2000_: *mut crate::leanh::LeanObject,
    mut v_a_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceHandler(v_declNames_1998_, v_a_1999_, v_a_2000_);
    crate::leanh::lean_dec(v_a_2000_);
    crate::leanh::lean_dec_ref(v_a_1999_);
    crate::leanh::lean_dec_ref(v_declNames_1998_);
    return v_res_2002_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = crate::leanh::lean_unsigned_to_nat(3244286355);
    v___x_2056_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__19_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
    v___x_2057_ = l_Lean_Name_num___override(v___x_2056_, v___x_2055_);
    return v___x_2057_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__21_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
    v___x_2060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__20_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
    v___x_2061_ = l_Lean_Name_str___override(v___x_2060_, v___x_2059_);
    return v___x_2061_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__23_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
    v___x_2064_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__22_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
    v___x_2065_ = l_Lean_Name_str___override(v___x_2064_, v___x_2063_);
    return v___x_2065_;
}
pub unsafe fn _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2066_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__24_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
    v___x_2068_ = l_Lean_Name_num___override(v___x_2067_, v___x_2066_);
    return v___x_2068_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2070_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__3;
    v___x_2071_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__0_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_;
    v___x_2072_ = l_Lean_Elab_registerDerivingHandler(v___x_2070_, v___x_2071_);
    if crate::leanh::lean_obj_tag(v___x_2072_) == 0 {
        let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2074_: u8 = 0;
        let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2072_, 1);
        v___x_2073_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_mkLawfulBEqInstanceCmds___closed__80;
        v___x_2074_ = 0;
        v___x_2075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn___closed__25_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_);
        v___x_2076_ = l_Lean_registerTraceClass(v___x_2073_, v___x_2074_, v___x_2075_);
        return v___x_2076_;
    } else {
        return v___x_2072_;
    }
}
pub unsafe fn l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2____boxed(
    mut v_a_2077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
    return v_res_2078_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_LawfulBEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_LawfulBEq_0__Lean_Elab_Deriving_LawfulBEq_initFn_00___x40_Lean_Elab_Deriving_LawfulBEq_3244286355____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_LawfulBEq(
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
pub unsafe fn initialize_Lean_Elab_Deriving_LawfulBEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
}
