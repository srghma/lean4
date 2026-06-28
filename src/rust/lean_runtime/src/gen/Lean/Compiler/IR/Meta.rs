// Lean compiler output
// Module: Lean.Compiler.IR.Meta
// Imports: Lean.Compiler.IR.CompilerM
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::IR::Basic::{
    l_Lean_IR_Alt_body, l_Lean_IR_Decl_name, l_Lean_IR_FnBody_body, l_Lean_IR_FnBody_isTerminal,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, l_Lean_IR_findLocalDecl___redArg,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::MetaAttr::{
    l_Lean_getIRPhases, l_Lean_isDeclMeta, l_Lean_isMarkedMeta, l_Lean_setDeclMeta,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::l_Lean_Environment_header;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Setup::l_Lean_instBEqIRPhases_beq;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 102, 101, 114, 77, 101, 116, 97, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,14541074971161486361 as *mut crate::leanh::LeanObject] };
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value) as *mut crate::leanh::LeanObject,7476836525069983911 as *mut crate::leanh::LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,16893283750695020466 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 97, 114, 107, 105, 110, 103, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [32, 97, 115, 32, 109, 101, 116, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 96, 109, 101, 116, 97, 96, 32, 99, 108, 111, 115, 117, 114, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [32, 97, 115, 32, 109, 101, 116, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value:
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
        67, 97, 110, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 99, 111, 110,
        115, 116, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        96, 32, 97, 115, 32, 105, 116, 32, 105, 115, 32, 110, 101, 105, 116, 104, 101, 114, 32,
        109, 97, 114, 107, 101, 100, 32, 110, 111, 114, 32, 105, 109, 112, 111, 114, 116, 101, 100,
        32, 97, 115, 32, 96, 109, 101, 116, 97, 96, 0,
    ],
};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [73, 82, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5089948989189718287 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2612642190274098415 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14881467155076526594 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9673106273749177955 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2025047596341339288 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11166744516247754581 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3503854797696231400 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13547387628543101761 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,792900073553451951 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6967373642037561092 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1709309148124196568 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(
    mut v_f_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = crate::leanh::lean_box(0);
    v___x_499_ = l_Lean_NameSet_insert(v_a_497_, v_f_496_);
    v___x_500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_500_, 0, v___x_498_);
    crate::leanh::lean_ctor_set(v___x_500_, 1, v___x_499_);
    return v___x_500_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(
    mut v_a_501_: *mut crate::leanh::LeanObject,
    mut v_a_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u8 = 0;
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: usize = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_501_) {
                0 => {
                    v_e_503_ = crate::leanh::lean_ctor_get(v_a_501_, 2);
                    crate::leanh::lean_inc_ref(v_e_503_);
                    v_b_504_ = crate::leanh::lean_ctor_get(v_a_501_, 3);
                    crate::leanh::lean_inc(v_b_504_);
                    crate::leanh::lean_dec_ref_known(v_a_501_, 4);
                    match crate::leanh::lean_obj_tag(v_e_503_) {
                        6 => {
                            v_c_511_ = crate::leanh::lean_ctor_get(v_e_503_, 0);
                            crate::leanh::lean_inc(v_c_511_);
                            crate::leanh::lean_dec_ref_known(v_e_503_, 2);
                            v_f_506_ = v_c_511_;
                            v___y_507_ = v_a_502_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_c_512_ = crate::leanh::lean_ctor_get(v_e_503_, 0);
                            crate::leanh::lean_inc(v_c_512_);
                            crate::leanh::lean_dec_ref_known(v_e_503_, 2);
                            v_f_506_ = v_c_512_;
                            v___y_507_ = v_a_502_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_e_503_);
                            v_a_501_ = v_b_504_;
                            state = 0;
                            continue;
                        }
                    }
                }
                1 => {
                    v_v_514_ = crate::leanh::lean_ctor_get(v_a_501_, 2);
                    crate::leanh::lean_inc(v_v_514_);
                    v_b_515_ = crate::leanh::lean_ctor_get(v_a_501_, 3);
                    crate::leanh::lean_inc(v_b_515_);
                    crate::leanh::lean_dec_ref_known(v_a_501_, 4);
                    v___x_516_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v_v_514_, v_a_502_);
                    v_snd_517_ = crate::leanh::lean_ctor_get(v___x_516_, 1);
                    crate::leanh::lean_inc(v_snd_517_);
                    crate::leanh::lean_dec_ref(v___x_516_);
                    v_a_501_ = v_b_515_;
                    v_a_502_ = v_snd_517_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_cs_519_ = crate::leanh::lean_ctor_get(v_a_501_, 3);
                    crate::leanh::lean_inc_ref(v_cs_519_);
                    crate::leanh::lean_dec_ref_known(v_a_501_, 4);
                    v___x_520_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_521_ = lean_array_get_size(v_cs_519_);
                    v___x_522_ = crate::leanh::lean_box(0);
                    v___x_523_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
                    if v___x_523_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_519_);
                        v___x_524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_524_, 0, v___x_522_);
                        crate::leanh::lean_ctor_set(v___x_524_, 1, v_a_502_);
                        return v___x_524_;
                    } else {
                        v___x_525_ = lean_nat_dec_le(v___x_521_, v___x_521_);
                        if v___x_525_ == 0 {
                            if v___x_523_ == 0 {
                                crate::leanh::lean_dec_ref(v_cs_519_);
                                v___x_526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_526_, 0, v___x_522_);
                                crate::leanh::lean_ctor_set(v___x_526_, 1, v_a_502_);
                                return v___x_526_;
                            } else {
                                v___x_527_ = 0usize;
                                v___x_528_ = lean_usize_of_nat(v___x_521_);
                                v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_519_, v___x_527_, v___x_528_, v___x_522_, v_a_502_);
                                crate::leanh::lean_dec_ref(v_cs_519_);
                                return v___x_529_;
                            }
                        } else {
                            v___x_530_ = 0usize;
                            v___x_531_ = lean_usize_of_nat(v___x_521_);
                            v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_519_, v___x_530_, v___x_531_, v___x_522_, v_a_502_);
                            crate::leanh::lean_dec_ref(v_cs_519_);
                            return v___x_532_;
                        }
                    }
                }
                _ => {
                    v___x_533_ = l_Lean_IR_FnBody_isTerminal(v_a_501_);
                    if v___x_533_ == 0 {
                        v___x_534_ = l_Lean_IR_FnBody_body(v_a_501_);
                        crate::leanh::lean_dec(v_a_501_);
                        v_a_501_ = v___x_534_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_501_);
                        v___x_536_ = crate::leanh::lean_box(0);
                        v___x_537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_537_, 0, v___x_536_);
                        crate::leanh::lean_ctor_set(v___x_537_, 1, v_a_502_);
                        return v___x_537_;
                    }
                }
            },
            1 => {
                v___x_508_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(
                    v_f_506_, v___y_507_,
                );
                v_snd_509_ = crate::leanh::lean_ctor_get(v___x_508_, 1);
                crate::leanh::lean_inc(v_snd_509_);
                crate::leanh::lean_dec_ref(v___x_508_);
                v_a_501_ = v_b_504_;
                v_a_502_ = v_snd_509_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(
    mut v_as_538_: *mut crate::leanh::LeanObject,
    mut v_i_539_: usize,
    mut v_stop_540_: usize,
    mut v_b_541_: *mut crate::leanh::LeanObject,
    mut v___y_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_543_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
                if v___x_543_ == 0 {
                    v___x_544_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
                    v___x_545_ = l_Lean_IR_Alt_body(v___x_544_);
                    v___x_546_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v___x_545_, v___y_542_);
                    v_fst_547_ = crate::leanh::lean_ctor_get(v___x_546_, 0);
                    crate::leanh::lean_inc(v_fst_547_);
                    v_snd_548_ = crate::leanh::lean_ctor_get(v___x_546_, 1);
                    crate::leanh::lean_inc(v_snd_548_);
                    crate::leanh::lean_dec_ref(v___x_546_);
                    v___x_549_ = 1usize;
                    v___x_550_ = lean_usize_add(v_i_539_, v___x_549_);
                    v_i_539_ = v___x_550_;
                    v_b_541_ = v_fst_547_;
                    v___y_542_ = v_snd_548_;
                    state = 0;
                    continue;
                } else {
                    v___x_552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_552_, 0, v_b_541_);
                    crate::leanh::lean_ctor_set(v___x_552_, 1, v___y_542_);
                    return v___x_552_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0___boxed(
    mut v_as_553_: *mut crate::leanh::LeanObject,
    mut v_i_554_: *mut crate::leanh::LeanObject,
    mut v_stop_555_: *mut crate::leanh::LeanObject,
    mut v_b_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_558_: usize = 0;
    let mut v_stop_boxed_559_: usize = 0;
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_558_ = crate::leanh::lean_unbox_usize(v_i_554_);
    crate::leanh::lean_dec(v_i_554_);
    v_stop_boxed_559_ = crate::leanh::lean_unbox_usize(v_stop_555_);
    crate::leanh::lean_dec(v_stop_555_);
    v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_as_553_, v_i_boxed_558_, v_stop_boxed_559_, v_b_556_, v___y_557_);
    crate::leanh::lean_dec_ref(v_as_553_);
    return v_res_560_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_561_) == 0 {
        let mut v_body_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_body_563_ = crate::leanh::lean_ctor_get(v_a_561_, 3);
        crate::leanh::lean_inc(v_body_563_);
        crate::leanh::lean_dec_ref_known(v_a_561_, 5);
        v___x_564_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(
            v_body_563_,
            v_a_562_,
        );
        return v___x_564_;
    } else {
        let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_a_561_, 4);
        v___x_565_ = crate::leanh::lean_box(0);
        v___x_566_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_566_, 0, v___x_565_);
        crate::leanh::lean_ctor_set(v___x_566_, 1, v_a_562_);
        return v___x_566_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(
    mut v_decl_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_568_ = l_Lean_NameSet_empty;
    v___x_569_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(
        v_decl_567_,
        v___x_568_,
    );
    v_snd_570_ = crate::leanh::lean_ctor_get(v___x_569_, 1);
    crate::leanh::lean_inc(v_snd_570_);
    crate::leanh::lean_dec_ref(v___x_569_);
    return v_snd_570_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_571_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_571_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0);
    v___x_573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_573_, 0, v___x_572_);
    return v___x_573_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
    v___x_575_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_576_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_575_);
    crate::leanh::lean_ctor_set(v___x_576_, 1, v___x_575_);
    crate::leanh::lean_ctor_set(v___x_576_, 2, v___x_575_);
    crate::leanh::lean_ctor_set(v___x_576_, 3, v___x_575_);
    crate::leanh::lean_ctor_set(v___x_576_, 4, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_576_, 5, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_576_, 6, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_576_, 7, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_576_, 8, v___x_574_);
    crate::leanh::lean_ctor_set(v___x_576_, 9, v___x_574_);
    return v___x_576_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_577_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
    v___x_579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_578_);
    return v___x_579_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_580_: usize = 0;
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = 5usize;
    v___x_581_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_582_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
    v___x_584_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3);
    v___x_585_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_585_, 0, v___x_584_);
    crate::leanh::lean_ctor_set(v___x_585_, 1, v___x_583_);
    crate::leanh::lean_ctor_set(v___x_585_, 2, v___x_581_);
    crate::leanh::lean_ctor_set(v___x_585_, 3, v___x_581_);
    crate::leanh::lean_ctor_set_usize(v___x_585_, 4, v___x_580_);
    return v___x_585_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = crate::leanh::lean_box(1);
    v___x_587_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4);
    v___x_588_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
    v___x_589_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_589_, 0, v___x_588_);
    crate::leanh::lean_ctor_set(v___x_589_, 1, v___x_587_);
    crate::leanh::lean_ctor_set(v___x_589_, 2, v___x_586_);
    return v___x_589_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(
    mut v_msgData_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
    mut v___y_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = lean_st_ref_get(v___y_592_);
    v_env_595_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
    crate::leanh::lean_inc_ref(v_env_595_);
    crate::leanh::lean_dec(v___x_594_);
    v_options_596_ = crate::leanh::lean_ctor_get(v___y_591_, 2);
    v___x_597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2);
    v___x_598_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_596_);
    v___x_599_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_599_, 0, v_env_595_);
    crate::leanh::lean_ctor_set(v___x_599_, 1, v___x_597_);
    crate::leanh::lean_ctor_set(v___x_599_, 2, v___x_598_);
    crate::leanh::lean_ctor_set(v___x_599_, 3, v_options_596_);
    v___x_600_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_600_, 0, v___x_599_);
    crate::leanh::lean_ctor_set(v___x_600_, 1, v_msgData_590_);
    v___x_601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_601_, 0, v___x_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___boxed(
    mut v_msgData_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_606_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msgData_602_, v___y_603_, v___y_604_);
    crate::leanh::lean_dec(v___y_604_);
    crate::leanh::lean_dec_ref(v___y_603_);
    return v_res_606_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0()
-> f64 {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: f64 = 0.0;
    v___x_607_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_608_ = lean_float_of_nat(v___x_607_);
    return v___x_608_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(
    mut v_cls_612_: *mut crate::leanh::LeanObject,
    mut v_msg_613_: *mut crate::leanh::LeanObject,
    mut v___y_614_: *mut crate::leanh::LeanObject,
    mut v___y_615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v_tid_636_: u64 = 0;
    let mut v_traces_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: f64 = 0.0;
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_617_ = crate::leanh::lean_ctor_get(v___y_614_, 5);
                v___x_618_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msg_613_, v___y_614_, v___y_615_);
                v_a_619_ = crate::leanh::lean_ctor_get(v___x_618_, 0);
                v_isSharedCheck_663_ = (!crate::leanh::lean_is_exclusive(v___x_618_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v___x_621_ = v___x_618_;
                    v_isShared_622_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_619_);
                    crate::leanh::lean_dec(v___x_618_);
                    v___x_621_ = crate::leanh::lean_box(0);
                    v_isShared_622_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_623_ = lean_st_ref_take(v___y_615_);
                v_traceState_624_ = crate::leanh::lean_ctor_get(v___x_623_, 4);
                v_env_625_ = crate::leanh::lean_ctor_get(v___x_623_, 0);
                v_nextMacroScope_626_ = crate::leanh::lean_ctor_get(v___x_623_, 1);
                v_ngen_627_ = crate::leanh::lean_ctor_get(v___x_623_, 2);
                v_auxDeclNGen_628_ = crate::leanh::lean_ctor_get(v___x_623_, 3);
                v_cache_629_ = crate::leanh::lean_ctor_get(v___x_623_, 5);
                v_messages_630_ = crate::leanh::lean_ctor_get(v___x_623_, 6);
                v_infoState_631_ = crate::leanh::lean_ctor_get(v___x_623_, 7);
                v_snapshotTasks_632_ = crate::leanh::lean_ctor_get(v___x_623_, 8);
                v_isSharedCheck_662_ = (!crate::leanh::lean_is_exclusive(v___x_623_)) as u8;
                if v_isSharedCheck_662_ == 0 {
                    v___x_634_ = v___x_623_;
                    v_isShared_635_ = v_isSharedCheck_662_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_632_);
                    crate::leanh::lean_inc(v_infoState_631_);
                    crate::leanh::lean_inc(v_messages_630_);
                    crate::leanh::lean_inc(v_cache_629_);
                    crate::leanh::lean_inc(v_traceState_624_);
                    crate::leanh::lean_inc(v_auxDeclNGen_628_);
                    crate::leanh::lean_inc(v_ngen_627_);
                    crate::leanh::lean_inc(v_nextMacroScope_626_);
                    crate::leanh::lean_inc(v_env_625_);
                    crate::leanh::lean_dec(v___x_623_);
                    v___x_634_ = crate::leanh::lean_box(0);
                    v_isShared_635_ = v_isSharedCheck_662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_636_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_624_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_637_ = crate::leanh::lean_ctor_get(v_traceState_624_, 0);
                v_isSharedCheck_661_ = (!crate::leanh::lean_is_exclusive(v_traceState_624_)) as u8;
                if v_isSharedCheck_661_ == 0 {
                    v___x_639_ = v_traceState_624_;
                    v_isShared_640_ = v_isSharedCheck_661_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_637_);
                    crate::leanh::lean_dec(v_traceState_624_);
                    v___x_639_ = crate::leanh::lean_box(0);
                    v_isShared_640_ = v_isSharedCheck_661_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_641_ = crate::leanh::lean_box(0);
                v___x_642_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0);
                v___x_643_ = 0;
                v___x_644_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1;
                v___x_645_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_645_, 0, v_cls_612_);
                crate::leanh::lean_ctor_set(v___x_645_, 1, v___x_641_);
                crate::leanh::lean_ctor_set(v___x_645_, 2, v___x_644_);
                crate::leanh::lean_ctor_set_float(
                    v___x_645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_642_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_642_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_645_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_643_,
                );
                v___x_646_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2;
                v___x_647_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_647_, 0, v___x_645_);
                crate::leanh::lean_ctor_set(v___x_647_, 1, v_a_619_);
                crate::leanh::lean_ctor_set(v___x_647_, 2, v___x_646_);
                crate::leanh::lean_inc(v_ref_617_);
                v___x_648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_648_, 0, v_ref_617_);
                crate::leanh::lean_ctor_set(v___x_648_, 1, v___x_647_);
                v___x_649_ = l_Lean_PersistentArray_push___redArg(v_traces_637_, v___x_648_);
                if v_isShared_640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_639_, 0, v___x_649_);
                    v___x_651_ = v___x_639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_649_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_660_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_636_,
                    );
                    v___x_651_ = v_reuseFailAlloc_660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_634_, 4, v___x_651_);
                    v___x_653_ = v___x_634_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v_env_625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 1, v_nextMacroScope_626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 2, v_ngen_627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 3, v_auxDeclNGen_628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 4, v___x_651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 5, v_cache_629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 6, v_messages_630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 7, v_infoState_631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 8, v_snapshotTasks_632_);
                    v___x_653_ = v_reuseFailAlloc_659_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_654_ = lean_st_ref_set(v___y_615_, v___x_653_);
                v___x_655_ = crate::leanh::lean_box(0);
                if v_isShared_622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_621_, 0, v___x_655_);
                    v___x_657_ = v___x_621_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
                    v___x_657_ = v_reuseFailAlloc_658_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___boxed(
    mut v_cls_664_: *mut crate::leanh::LeanObject,
    mut v_msg_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
    mut v___y_667_: *mut crate::leanh::LeanObject,
    mut v___y_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_669_ =
        l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(
            v_cls_664_, v_msg_665_, v___y_666_, v___y_667_,
        );
    crate::leanh::lean_dec(v___y_667_);
    crate::leanh::lean_dec_ref(v___y_666_);
    return v_res_669_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_670_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0);
    v___x_672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1);
    v___x_674_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
    crate::leanh::lean_ctor_set(v___x_674_, 1, v___x_673_);
    return v___x_674_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
    v___x_686_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8;
    v___x_687_ = l_Lean_Name_append(v___x_686_, v___x_685_);
    return v___x_687_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10;
    v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
    return v___x_690_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12;
    v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
    return v___x_693_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(
    mut v_init_694_: *mut crate::leanh::LeanObject,
    mut v_x_695_: *mut crate::leanh::LeanObject,
    mut v___y_696_: *mut crate::leanh::LeanObject,
    mut v___y_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_735_: u8 = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_739_: u8 = 0;
    let mut v_reuseFailAlloc_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_744_: u8 = 0;
    let mut v_inheritedTraceOptions_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut v_a_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_771_: u8 = 0;
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_695_) == 0 {
                    v_k_699_ = crate::leanh::lean_ctor_get(v_x_695_, 1);
                    crate::leanh::lean_inc(v_k_699_);
                    v_l_700_ = crate::leanh::lean_ctor_get(v_x_695_, 3);
                    crate::leanh::lean_inc(v_l_700_);
                    v_r_701_ = crate::leanh::lean_ctor_get(v_x_695_, 4);
                    crate::leanh::lean_inc(v_r_701_);
                    crate::leanh::lean_dec_ref_known(v_x_695_, 5);
                    v___x_702_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_694_, v_l_700_, v___y_696_, v___y_697_);
                    if crate::leanh::lean_obj_tag(v___x_702_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_702_, 1);
                        v___x_703_ = lean_st_ref_get(v___y_697_);
                        v_env_704_ = crate::leanh::lean_ctor_get(v___x_703_, 0);
                        crate::leanh::lean_inc_ref(v_env_704_);
                        crate::leanh::lean_dec(v___x_703_);
                        v___x_705_ = crate::leanh::lean_box(0);
                        v___x_706_ = l_Lean_isDeclMeta(v_env_704_, v_k_699_);
                        if v___x_706_ == 0 {
                            v___x_707_ = l_Lean_IR_findLocalDecl___redArg(v_k_699_, v___y_697_);
                            if crate::leanh::lean_obj_tag(v___x_707_) == 0 {
                                v_a_708_ = crate::leanh::lean_ctor_get(v___x_707_, 0);
                                crate::leanh::lean_inc(v_a_708_);
                                crate::leanh::lean_dec_ref_known(v___x_707_, 1);
                                if crate::leanh::lean_obj_tag(v_a_708_) == 1 {
                                    v_val_709_ = crate::leanh::lean_ctor_get(v_a_708_, 0);
                                    crate::leanh::lean_inc(v_val_709_);
                                    crate::leanh::lean_dec_ref_known(v_a_708_, 1);
                                    v_options_743_ = crate::leanh::lean_ctor_get(v___y_696_, 2);
                                    v_hasTrace_744_ = crate::leanh::lean_ctor_get_uint8(
                                        v_options_743_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                            as u32,
                                    );
                                    if v_hasTrace_744_ == 0 {
                                        v___y_711_ = v___y_696_;
                                        v___y_712_ = v___y_697_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_inheritedTraceOptions_745_ =
                                            crate::leanh::lean_ctor_get(v___y_696_, 13);
                                        v___x_746_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
                                        v___x_747_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
                                        v___x_748_ =
                                            l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                                v_inheritedTraceOptions_745_,
                                                v_options_743_,
                                                v___x_747_,
                                            );
                                        if v___x_748_ == 0 {
                                            v___y_711_ = v___y_696_;
                                            v___y_712_ = v___y_697_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
                                            crate::leanh::lean_inc(v_k_699_);
                                            v___x_750_ = l_Lean_MessageData_ofName(v_k_699_);
                                            v___x_751_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_751_, 0, v___x_749_);
                                            crate::leanh::lean_ctor_set(v___x_751_, 1, v___x_750_);
                                            v___x_752_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13);
                                            v___x_753_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_753_, 0, v___x_751_);
                                            crate::leanh::lean_ctor_set(v___x_753_, 1, v___x_752_);
                                            v___x_754_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_746_, v___x_753_, v___y_696_, v___y_697_);
                                            if crate::leanh::lean_obj_tag(v___x_754_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_754_, 1);
                                                v___y_711_ = v___y_696_;
                                                v___y_712_ = v___y_697_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_val_709_);
                                                crate::leanh::lean_dec(v_r_701_);
                                                crate::leanh::lean_dec(v_k_699_);
                                                v_a_755_ =
                                                    crate::leanh::lean_ctor_get(v___x_754_, 0);
                                                v_isSharedCheck_762_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_754_))
                                                        as u8;
                                                if v_isSharedCheck_762_ == 0 {
                                                    v___x_757_ = v___x_754_;
                                                    v_isShared_758_ = v_isSharedCheck_762_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_755_);
                                                    crate::leanh::lean_dec(v___x_754_);
                                                    v___x_757_ = crate::leanh::lean_box(0);
                                                    v_isShared_758_ = v_isSharedCheck_762_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_708_);
                                    crate::leanh::lean_dec(v_k_699_);
                                    v_init_694_ = v___x_705_;
                                    v_x_695_ = v_r_701_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_r_701_);
                                crate::leanh::lean_dec(v_k_699_);
                                v_a_764_ = crate::leanh::lean_ctor_get(v___x_707_, 0);
                                v_isSharedCheck_771_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_707_)) as u8;
                                if v_isSharedCheck_771_ == 0 {
                                    v___x_766_ = v___x_707_;
                                    v_isShared_767_ = v_isSharedCheck_771_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_764_);
                                    crate::leanh::lean_dec(v___x_707_);
                                    v___x_766_ = crate::leanh::lean_box(0);
                                    v_isShared_767_ = v_isSharedCheck_771_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_k_699_);
                            v_init_694_ = v___x_705_;
                            v_x_695_ = v_r_701_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_r_701_);
                        crate::leanh::lean_dec(v_k_699_);
                        return v___x_702_;
                    }
                } else {
                    v___x_773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_773_, 0, v_init_694_);
                    v___x_774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_774_, 0, v___x_773_);
                    return v___x_774_;
                }
            }
            1 => {
                v___x_713_ = lean_st_ref_take(v___y_712_);
                v_env_714_ = crate::leanh::lean_ctor_get(v___x_713_, 0);
                v_nextMacroScope_715_ = crate::leanh::lean_ctor_get(v___x_713_, 1);
                v_ngen_716_ = crate::leanh::lean_ctor_get(v___x_713_, 2);
                v_auxDeclNGen_717_ = crate::leanh::lean_ctor_get(v___x_713_, 3);
                v_traceState_718_ = crate::leanh::lean_ctor_get(v___x_713_, 4);
                v_messages_719_ = crate::leanh::lean_ctor_get(v___x_713_, 6);
                v_infoState_720_ = crate::leanh::lean_ctor_get(v___x_713_, 7);
                v_snapshotTasks_721_ = crate::leanh::lean_ctor_get(v___x_713_, 8);
                v_isSharedCheck_741_ = (!crate::leanh::lean_is_exclusive(v___x_713_)) as u8;
                if v_isSharedCheck_741_ == 0 {
                    v_unused_742_ = crate::leanh::lean_ctor_get(v___x_713_, 5);
                    crate::leanh::lean_dec(v_unused_742_);
                    v___x_723_ = v___x_713_;
                    v_isShared_724_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_721_);
                    crate::leanh::lean_inc(v_infoState_720_);
                    crate::leanh::lean_inc(v_messages_719_);
                    crate::leanh::lean_inc(v_traceState_718_);
                    crate::leanh::lean_inc(v_auxDeclNGen_717_);
                    crate::leanh::lean_inc(v_ngen_716_);
                    crate::leanh::lean_inc(v_nextMacroScope_715_);
                    crate::leanh::lean_inc(v_env_714_);
                    crate::leanh::lean_dec(v___x_713_);
                    v___x_723_ = crate::leanh::lean_box(0);
                    v_isShared_724_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_725_ = l_Lean_setDeclMeta(v_env_714_, v_k_699_);
                v___x_726_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
                if v_isShared_724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_723_, 5, v___x_726_);
                    crate::leanh::lean_ctor_set(v___x_723_, 0, v___x_725_);
                    v___x_728_ = v___x_723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 1, v_nextMacroScope_715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 2, v_ngen_716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 3, v_auxDeclNGen_717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 4, v_traceState_718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 5, v___x_726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 6, v_messages_719_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 7, v_infoState_720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_740_, 8, v_snapshotTasks_721_);
                    v___x_728_ = v_reuseFailAlloc_740_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_729_ = lean_st_ref_set(v___y_712_, v___x_728_);
                v___x_730_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
                    v_val_709_, v___y_711_, v___y_712_,
                );
                if crate::leanh::lean_obj_tag(v___x_730_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_730_, 1);
                    v_init_694_ = v___x_705_;
                    v_x_695_ = v_r_701_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_701_);
                    v_a_732_ = crate::leanh::lean_ctor_get(v___x_730_, 0);
                    v_isSharedCheck_739_ = (!crate::leanh::lean_is_exclusive(v___x_730_)) as u8;
                    if v_isSharedCheck_739_ == 0 {
                        v___x_734_ = v___x_730_;
                        v_isShared_735_ = v_isSharedCheck_739_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_732_);
                        crate::leanh::lean_dec(v___x_730_);
                        v___x_734_ = crate::leanh::lean_box(0);
                        v_isShared_735_ = v_isSharedCheck_739_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_735_ == 0 {
                    v___x_737_ = v___x_734_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
                    v___x_737_ = v_reuseFailAlloc_738_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_737_;
            }
            6 => {
                if v_isShared_758_ == 0 {
                    v___x_760_ = v___x_757_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
                    v___x_760_ = v_reuseFailAlloc_761_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_760_;
            }
            8 => {
                if v_isShared_767_ == 0 {
                    v___x_769_ = v___x_766_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
                    v___x_769_ = v_reuseFailAlloc_770_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
    mut v_decl_775_: *mut crate::leanh::LeanObject,
    mut v_a_776_: *mut crate::leanh::LeanObject,
    mut v_a_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut v_unused_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_779_ =
                    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(v_decl_775_);
                v___x_780_ = crate::leanh::lean_box(0);
                v___x_781_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_780_, v___x_779_, v_a_776_, v_a_777_);
                if crate::leanh::lean_obj_tag(v___x_781_) == 0 {
                    v_isSharedCheck_788_ = (!crate::leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_788_ == 0 {
                        v_unused_789_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                        crate::leanh::lean_dec(v_unused_789_);
                        v___x_783_ = v___x_781_;
                        v_isShared_784_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_781_);
                        v___x_783_ = crate::leanh::lean_box(0);
                        v_isShared_784_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_790_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_797_ = (!crate::leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v___x_792_ = v___x_781_;
                        v_isShared_793_ = v_isSharedCheck_797_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_790_);
                        crate::leanh::lean_dec(v___x_781_);
                        v___x_792_ = crate::leanh::lean_box(0);
                        v_isShared_793_ = v_isSharedCheck_797_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_784_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_783_, 0, v___x_780_);
                    v___x_786_ = v___x_783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_780_);
                    v___x_786_ = v_reuseFailAlloc_787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_786_;
            }
            3 => {
                if v_isShared_793_ == 0 {
                    v___x_795_ = v___x_792_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
                    v___x_795_ = v_reuseFailAlloc_796_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(
    mut v_decl_798_: *mut crate::leanh::LeanObject,
    mut v_a_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
        v_decl_798_,
        v_a_799_,
        v_a_800_,
    );
    crate::leanh::lean_dec(v_a_800_);
    crate::leanh::lean_dec_ref(v_a_799_);
    return v_res_802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(
    mut v_init_803_: *mut crate::leanh::LeanObject,
    mut v_x_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_803_, v_x_804_, v___y_805_, v___y_806_);
    crate::leanh::lean_dec(v___y_806_);
    crate::leanh::lean_dec_ref(v___y_805_);
    return v_res_808_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0;
    v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
    return v___x_811_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(
    mut v_as_812_: *mut crate::leanh::LeanObject,
    mut v_sz_813_: usize,
    mut v_i_814_: usize,
    mut v_b_815_: *mut crate::leanh::LeanObject,
    mut v___y_816_: *mut crate::leanh::LeanObject,
    mut v___y_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: usize = 0;
    let mut v___x_822_: usize = 0;
    let mut v___x_824_: u8 = 0;
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_845_: u8 = 0;
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_853_: u8 = 0;
    let mut v_unused_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v_options_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_857_: u8 = 0;
    let mut v_inheritedTraceOptions_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_824_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
                if v___x_824_ == 0 {
                    v___x_825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_825_, 0, v_b_815_);
                    return v___x_825_;
                } else {
                    v___x_826_ = lean_st_ref_get(v___y_817_);
                    v_env_827_ = crate::leanh::lean_ctor_get(v___x_826_, 0);
                    crate::leanh::lean_inc_ref(v_env_827_);
                    crate::leanh::lean_dec(v___x_826_);
                    v___x_828_ = crate::leanh::lean_box(0);
                    v_a_829_ = lean_array_uget_borrowed(v_as_812_, v_i_814_);
                    v___x_830_ = l_Lean_IR_Decl_name(v_a_829_);
                    crate::leanh::lean_inc(v___x_830_);
                    v___x_855_ = l_Lean_isMarkedMeta(v_env_827_, v___x_830_);
                    if v___x_855_ == 0 {
                        crate::leanh::lean_dec(v___x_830_);
                        v_a_820_ = v___x_828_;
                        state = 1;
                        continue;
                    } else {
                        v_options_856_ = crate::leanh::lean_ctor_get(v___y_816_, 2);
                        v_hasTrace_857_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_856_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_857_ == 0 {
                            v___y_832_ = v___y_816_;
                            v___y_833_ = v___y_817_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_858_ =
                                crate::leanh::lean_ctor_get(v___y_816_, 13);
                            v___x_859_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
                            v___x_860_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
                            v___x_861_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_858_,
                                v_options_856_,
                                v___x_860_,
                            );
                            if v___x_861_ == 0 {
                                v___y_832_ = v___y_816_;
                                v___y_833_ = v___y_817_;
                                state = 2;
                                continue;
                            } else {
                                v___x_862_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
                                crate::leanh::lean_inc(v___x_830_);
                                v___x_863_ = l_Lean_MessageData_ofName(v___x_830_);
                                v___x_864_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_864_, 0, v___x_862_);
                                crate::leanh::lean_ctor_set(v___x_864_, 1, v___x_863_);
                                v___x_865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1);
                                v___x_866_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_864_);
                                crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_865_);
                                v___x_867_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_859_, v___x_866_, v___y_816_, v___y_817_);
                                if crate::leanh::lean_obj_tag(v___x_867_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_867_, 1);
                                    v___y_832_ = v___y_816_;
                                    v___y_833_ = v___y_817_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_830_);
                                    return v___x_867_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_821_ = 1usize;
                v___x_822_ = lean_usize_add(v_i_814_, v___x_821_);
                v_i_814_ = v___x_822_;
                v_b_815_ = v_a_820_;
                state = 0;
                continue;
            }
            2 => {
                v___x_834_ = lean_st_ref_take(v___y_833_);
                v_env_835_ = crate::leanh::lean_ctor_get(v___x_834_, 0);
                v_nextMacroScope_836_ = crate::leanh::lean_ctor_get(v___x_834_, 1);
                v_ngen_837_ = crate::leanh::lean_ctor_get(v___x_834_, 2);
                v_auxDeclNGen_838_ = crate::leanh::lean_ctor_get(v___x_834_, 3);
                v_traceState_839_ = crate::leanh::lean_ctor_get(v___x_834_, 4);
                v_messages_840_ = crate::leanh::lean_ctor_get(v___x_834_, 6);
                v_infoState_841_ = crate::leanh::lean_ctor_get(v___x_834_, 7);
                v_snapshotTasks_842_ = crate::leanh::lean_ctor_get(v___x_834_, 8);
                v_isSharedCheck_853_ = (!crate::leanh::lean_is_exclusive(v___x_834_)) as u8;
                if v_isSharedCheck_853_ == 0 {
                    v_unused_854_ = crate::leanh::lean_ctor_get(v___x_834_, 5);
                    crate::leanh::lean_dec(v_unused_854_);
                    v___x_844_ = v___x_834_;
                    v_isShared_845_ = v_isSharedCheck_853_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_842_);
                    crate::leanh::lean_inc(v_infoState_841_);
                    crate::leanh::lean_inc(v_messages_840_);
                    crate::leanh::lean_inc(v_traceState_839_);
                    crate::leanh::lean_inc(v_auxDeclNGen_838_);
                    crate::leanh::lean_inc(v_ngen_837_);
                    crate::leanh::lean_inc(v_nextMacroScope_836_);
                    crate::leanh::lean_inc(v_env_835_);
                    crate::leanh::lean_dec(v___x_834_);
                    v___x_844_ = crate::leanh::lean_box(0);
                    v_isShared_845_ = v_isSharedCheck_853_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_846_ = l_Lean_setDeclMeta(v_env_835_, v___x_830_);
                v___x_847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
                if v_isShared_845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_844_, 5, v___x_847_);
                    crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_846_);
                    v___x_849_ = v___x_844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_852_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 1, v_nextMacroScope_836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 2, v_ngen_837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 3, v_auxDeclNGen_838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 4, v_traceState_839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 5, v___x_847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 6, v_messages_840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 7, v_infoState_841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 8, v_snapshotTasks_842_);
                    v___x_849_ = v_reuseFailAlloc_852_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_850_ = lean_st_ref_set(v___y_833_, v___x_849_);
                crate::leanh::lean_inc(v_a_829_);
                v___x_851_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
                    v_a_829_, v___y_832_, v___y_833_,
                );
                if crate::leanh::lean_obj_tag(v___x_851_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_851_, 1);
                    v_a_820_ = v___x_828_;
                    state = 1;
                    continue;
                } else {
                    return v___x_851_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___boxed(
    mut v_as_868_: *mut crate::leanh::LeanObject,
    mut v_sz_869_: *mut crate::leanh::LeanObject,
    mut v_i_870_: *mut crate::leanh::LeanObject,
    mut v_b_871_: *mut crate::leanh::LeanObject,
    mut v___y_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_875_: usize = 0;
    let mut v_i_boxed_876_: usize = 0;
    let mut v_res_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_875_ = crate::leanh::lean_unbox_usize(v_sz_869_);
    crate::leanh::lean_dec(v_sz_869_);
    v_i_boxed_876_ = crate::leanh::lean_unbox_usize(v_i_870_);
    crate::leanh::lean_dec(v_i_870_);
    v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_as_868_, v_sz_boxed_875_, v_i_boxed_876_, v_b_871_, v___y_872_, v___y_873_);
    crate::leanh::lean_dec(v___y_873_);
    crate::leanh::lean_dec_ref(v___y_872_);
    crate::leanh::lean_dec_ref(v_as_868_);
    return v_res_877_;
}
pub unsafe fn l_Lean_IR_inferMeta(
    mut v_decls_878_: *mut crate::leanh::LeanObject,
    mut v_a_879_: *mut crate::leanh::LeanObject,
    mut v_a_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isModule_885_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_889_: usize = 0;
    let mut v___x_890_: usize = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_894_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut v_unused_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_882_ = lean_st_ref_get(v_a_880_);
                v_env_883_ = crate::leanh::lean_ctor_get(v___x_882_, 0);
                crate::leanh::lean_inc_ref(v_env_883_);
                crate::leanh::lean_dec(v___x_882_);
                v___x_884_ = l_Lean_Environment_header(v_env_883_);
                crate::leanh::lean_dec_ref(v_env_883_);
                v_isModule_885_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_884_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 4) as u32,
                );
                crate::leanh::lean_dec_ref(v___x_884_);
                if v_isModule_885_ == 0 {
                    v___x_886_ = crate::leanh::lean_box(0);
                    v___x_887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_887_, 0, v___x_886_);
                    return v___x_887_;
                } else {
                    v___x_888_ = crate::leanh::lean_box(0);
                    v_sz_889_ = lean_array_size(v_decls_878_);
                    v___x_890_ = 0usize;
                    v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_decls_878_, v_sz_889_, v___x_890_, v___x_888_, v_a_879_, v_a_880_);
                    if crate::leanh::lean_obj_tag(v___x_891_) == 0 {
                        v_isSharedCheck_898_ = (!crate::leanh::lean_is_exclusive(v___x_891_)) as u8;
                        if v_isSharedCheck_898_ == 0 {
                            v_unused_899_ = crate::leanh::lean_ctor_get(v___x_891_, 0);
                            crate::leanh::lean_dec(v_unused_899_);
                            v___x_893_ = v___x_891_;
                            v_isShared_894_ = v_isSharedCheck_898_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_891_);
                            v___x_893_ = crate::leanh::lean_box(0);
                            v_isShared_894_ = v_isSharedCheck_898_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_891_;
                    }
                }
            }
            1 => {
                if v_isShared_894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_893_, 0, v___x_888_);
                    v___x_896_ = v___x_893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_888_);
                    v___x_896_ = v_reuseFailAlloc_897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_inferMeta___boxed(
    mut v_decls_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_a_902_: *mut crate::leanh::LeanObject,
    mut v_a_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_IR_inferMeta(v_decls_900_, v_a_901_, v_a_902_);
    crate::leanh::lean_dec(v_a_902_);
    crate::leanh::lean_dec_ref(v_a_901_);
    crate::leanh::lean_dec_ref(v_decls_900_);
    return v_res_904_;
}
pub unsafe fn lean_eval_check_meta(
    mut v_env_909_: *mut crate::leanh::LeanObject,
    mut v_declName_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: u8 = 0;
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: u8 = 0;
    crate::leanh::lean_inc(v_declName_910_);
    v___x_911_ = l_Lean_getIRPhases(v_env_909_, v_declName_910_);
    v___x_912_ = 0;
    v___x_913_ = l_Lean_instBEqIRPhases_beq(v___x_911_, v___x_912_);
    if v___x_913_ == 0 {
        let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declName_910_);
        v___x_914_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0;
        return v___x_914_;
    } else {
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_915_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1;
        v___x_916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_declName_910_,
            v___x_913_,
        );
        v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
        crate::leanh::lean_dec_ref(v___x_916_);
        v___x_918_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2;
        v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
        v___x_920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_920_, 0, v___x_919_);
        return v___x_920_;
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = crate::leanh::lean_unsigned_to_nat(3167601923);
    v___x_971_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_972_ = l_Lean_Name_num___override(v___x_971_, v___x_970_);
    return v___x_972_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_975_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_976_ = l_Lean_Name_str___override(v___x_975_, v___x_974_);
    return v___x_976_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_979_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_980_ = l_Lean_Name_str___override(v___x_979_, v___x_978_);
    return v___x_980_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_981_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_983_ = l_Lean_Name_num___override(v___x_982_, v___x_981_);
    return v___x_983_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
    v___x_986_ = 0;
    v___x_987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_988_ = l_Lean_registerTraceClass(v___x_985_, v___x_986_, v___x_987_);
    return v___x_988_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(
    mut v_a_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
    return v_res_990_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Meta(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Meta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Meta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Meta(builtin);
}
