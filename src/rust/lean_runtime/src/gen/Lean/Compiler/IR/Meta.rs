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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_float_once, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 102, 101, 114, 77, 101, 116, 97, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value) as *mut LeanObject;
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value) as *mut LeanObject,14541074971161486361 as *mut LeanObject] };
static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value) as *mut LeanObject,7476836525069983911 as *mut LeanObject] };
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value) as *mut LeanObject,16893283750695020466 as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [77, 97, 114, 107, 105, 110, 103, 32, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [32, 97, 115, 32, 109, 101, 116, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 96, 109, 101, 116, 97, 96, 32, 99, 108, 111, 115, 117, 114, 101, 0]};
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [32, 97, 115, 32, 109, 101, 116, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 109, 101, 116, 97, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [73, 82, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,5089948989189718287 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,2612642190274098415 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14881467155076526594 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,9673106273749177955 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,2025047596341339288 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,11166744516247754581 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,3503854797696231400 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,13547387628543101761 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,792900073553451951 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,6967373642037561092 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject,1709309148124196568 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(
    mut v_f_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    v___x_498_ = lean_box(0);
    v___x_499_ = l_Lean_NameSet_insert(v_a_497_, v_f_496_);
    v___x_500_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_500_, 0, v___x_498_);
    lean_ctor_set(v___x_500_, 1, v___x_499_);
    return v___x_500_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(
    mut v_a_501_: *mut LeanObject,
    mut v_a_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: u8 = 0;
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: u8 = 0;
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: usize = 0;
    let mut v___x_528_: usize = 0;
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: usize = 0;
    let mut v___x_531_: usize = 0;
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_501_) {
                0 => {
                    v_e_503_ = lean_ctor_get(v_a_501_, 2);
                    lean_inc_ref(v_e_503_);
                    v_b_504_ = lean_ctor_get(v_a_501_, 3);
                    lean_inc(v_b_504_);
                    lean_dec_ref_known(v_a_501_, 4);
                    match lean_obj_tag(v_e_503_) {
                        6 => {
                            v_c_511_ = lean_ctor_get(v_e_503_, 0);
                            lean_inc(v_c_511_);
                            lean_dec_ref_known(v_e_503_, 2);
                            v_f_506_ = v_c_511_;
                            v___y_507_ = v_a_502_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_c_512_ = lean_ctor_get(v_e_503_, 0);
                            lean_inc(v_c_512_);
                            lean_dec_ref_known(v_e_503_, 2);
                            v_f_506_ = v_c_512_;
                            v___y_507_ = v_a_502_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_e_503_);
                            v_a_501_ = v_b_504_;
                            state = 0;
                            continue;
                        }
                    }
                }
                1 => {
                    v_v_514_ = lean_ctor_get(v_a_501_, 2);
                    lean_inc(v_v_514_);
                    v_b_515_ = lean_ctor_get(v_a_501_, 3);
                    lean_inc(v_b_515_);
                    lean_dec_ref_known(v_a_501_, 4);
                    v___x_516_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v_v_514_, v_a_502_);
                    v_snd_517_ = lean_ctor_get(v___x_516_, 1);
                    lean_inc(v_snd_517_);
                    lean_dec_ref(v___x_516_);
                    v_a_501_ = v_b_515_;
                    v_a_502_ = v_snd_517_;
                    state = 0;
                    continue;
                }
                9 => {
                    v_cs_519_ = lean_ctor_get(v_a_501_, 3);
                    lean_inc_ref(v_cs_519_);
                    lean_dec_ref_known(v_a_501_, 4);
                    v___x_520_ = lean_unsigned_to_nat(0);
                    v___x_521_ = lean_array_get_size(v_cs_519_);
                    v___x_522_ = lean_box(0);
                    v___x_523_ = lean_nat_dec_lt(v___x_520_, v___x_521_);
                    if v___x_523_ == 0 {
                        lean_dec_ref(v_cs_519_);
                        v___x_524_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_524_, 0, v___x_522_);
                        lean_ctor_set(v___x_524_, 1, v_a_502_);
                        return v___x_524_;
                    } else {
                        v___x_525_ = lean_nat_dec_le(v___x_521_, v___x_521_);
                        if v___x_525_ == 0 {
                            if v___x_523_ == 0 {
                                lean_dec_ref(v_cs_519_);
                                v___x_526_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_526_, 0, v___x_522_);
                                lean_ctor_set(v___x_526_, 1, v_a_502_);
                                return v___x_526_;
                            } else {
                                v___x_527_ = 0usize;
                                v___x_528_ = lean_usize_of_nat(v___x_521_);
                                v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_519_, v___x_527_, v___x_528_, v___x_522_, v_a_502_);
                                lean_dec_ref(v_cs_519_);
                                return v___x_529_;
                            }
                        } else {
                            v___x_530_ = 0usize;
                            v___x_531_ = lean_usize_of_nat(v___x_521_);
                            v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_519_, v___x_530_, v___x_531_, v___x_522_, v_a_502_);
                            lean_dec_ref(v_cs_519_);
                            return v___x_532_;
                        }
                    }
                }
                _ => {
                    v___x_533_ = l_Lean_IR_FnBody_isTerminal(v_a_501_);
                    if v___x_533_ == 0 {
                        v___x_534_ = l_Lean_IR_FnBody_body(v_a_501_);
                        lean_dec(v_a_501_);
                        v_a_501_ = v___x_534_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_501_);
                        v___x_536_ = lean_box(0);
                        v___x_537_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_537_, 0, v___x_536_);
                        lean_ctor_set(v___x_537_, 1, v_a_502_);
                        return v___x_537_;
                    }
                }
            },
            1 => {
                v___x_508_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(
                    v_f_506_, v___y_507_,
                );
                v_snd_509_ = lean_ctor_get(v___x_508_, 1);
                lean_inc(v_snd_509_);
                lean_dec_ref(v___x_508_);
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
    mut v_as_538_: *mut LeanObject,
    mut v_i_539_: usize,
    mut v_stop_540_: usize,
    mut v_b_541_: *mut LeanObject,
    mut v___y_542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: u8 = 0;
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_543_ = lean_usize_dec_eq(v_i_539_, v_stop_540_);
                if v___x_543_ == 0 {
                    v___x_544_ = lean_array_uget_borrowed(v_as_538_, v_i_539_);
                    v___x_545_ = l_Lean_IR_Alt_body(v___x_544_);
                    v___x_546_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v___x_545_, v___y_542_);
                    v_fst_547_ = lean_ctor_get(v___x_546_, 0);
                    lean_inc(v_fst_547_);
                    v_snd_548_ = lean_ctor_get(v___x_546_, 1);
                    lean_inc(v_snd_548_);
                    lean_dec_ref(v___x_546_);
                    v___x_549_ = 1usize;
                    v___x_550_ = lean_usize_add(v_i_539_, v___x_549_);
                    v_i_539_ = v___x_550_;
                    v_b_541_ = v_fst_547_;
                    v___y_542_ = v_snd_548_;
                    state = 0;
                    continue;
                } else {
                    v___x_552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_552_, 0, v_b_541_);
                    lean_ctor_set(v___x_552_, 1, v___y_542_);
                    return v___x_552_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0___boxed(
    mut v_as_553_: *mut LeanObject,
    mut v_i_554_: *mut LeanObject,
    mut v_stop_555_: *mut LeanObject,
    mut v_b_556_: *mut LeanObject,
    mut v___y_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_558_: usize = 0;
    let mut v_stop_boxed_559_: usize = 0;
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_558_ = lean_unbox_usize(v_i_554_);
    lean_dec(v_i_554_);
    v_stop_boxed_559_ = lean_unbox_usize(v_stop_555_);
    lean_dec(v_stop_555_);
    v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_as_553_, v_i_boxed_558_, v_stop_boxed_559_, v_b_556_, v___y_557_);
    lean_dec_ref(v_as_553_);
    return v_res_560_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(
    mut v_a_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_561_) == 0 {
        let mut v_body_563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
        v_body_563_ = lean_ctor_get(v_a_561_, 3);
        lean_inc(v_body_563_);
        lean_dec_ref_known(v_a_561_, 5);
        v___x_564_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(
            v_body_563_,
            v_a_562_,
        );
        return v___x_564_;
    } else {
        let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_a_561_, 4);
        v___x_565_ = lean_box(0);
        v___x_566_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_566_, 0, v___x_565_);
        lean_ctor_set(v___x_566_, 1, v_a_562_);
        return v___x_566_;
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(
    mut v_decl_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_570_: *mut LeanObject = core::ptr::null_mut();
    v___x_568_ = l_Lean_NameSet_empty;
    v___x_569_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(
        v_decl_567_,
        v___x_568_,
    );
    v_snd_570_ = lean_ctor_get(v___x_569_, 1);
    lean_inc(v_snd_570_);
    lean_dec_ref(v___x_569_);
    return v_snd_570_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_571_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_571_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_572_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0);
    v___x_573_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_573_, 0, v___x_572_);
    return v___x_573_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
    v___x_575_ = lean_unsigned_to_nat(0);
    v___x_576_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_576_, 0, v___x_575_);
    lean_ctor_set(v___x_576_, 1, v___x_575_);
    lean_ctor_set(v___x_576_, 2, v___x_575_);
    lean_ctor_set(v___x_576_, 3, v___x_575_);
    lean_ctor_set(v___x_576_, 4, v___x_574_);
    lean_ctor_set(v___x_576_, 5, v___x_574_);
    lean_ctor_set(v___x_576_, 6, v___x_574_);
    lean_ctor_set(v___x_576_, 7, v___x_574_);
    lean_ctor_set(v___x_576_, 8, v___x_574_);
    lean_ctor_set(v___x_576_, 9, v___x_574_);
    return v___x_576_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ = lean_unsigned_to_nat(32);
    v___x_578_ = lean_mk_empty_array_with_capacity(v___x_577_);
    v___x_579_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_579_, 0, v___x_578_);
    return v___x_579_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_580_: usize = 0;
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = 5usize;
    v___x_581_ = lean_unsigned_to_nat(0);
    v___x_582_ = lean_unsigned_to_nat(32);
    v___x_583_ = lean_mk_empty_array_with_capacity(v___x_582_);
    v___x_584_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3);
    v___x_585_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_585_, 0, v___x_584_);
    lean_ctor_set(v___x_585_, 1, v___x_583_);
    lean_ctor_set(v___x_585_, 2, v___x_581_);
    lean_ctor_set(v___x_585_, 3, v___x_581_);
    lean_ctor_set_usize(v___x_585_, 4, v___x_580_);
    return v___x_585_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = lean_box(1);
    v___x_587_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4);
    v___x_588_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
    v___x_589_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_589_, 0, v___x_588_);
    lean_ctor_set(v___x_589_, 1, v___x_587_);
    lean_ctor_set(v___x_589_, 2, v___x_586_);
    return v___x_589_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(
    mut v_msgData_590_: *mut LeanObject,
    mut v___y_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_594_ = lean_st_ref_get(v___y_592_);
    v_env_595_ = lean_ctor_get(v___x_594_, 0);
    lean_inc_ref(v_env_595_);
    lean_dec(v___x_594_);
    v_options_596_ = lean_ctor_get(v___y_591_, 2);
    v___x_597_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2);
    v___x_598_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_596_);
    v___x_599_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_599_, 0, v_env_595_);
    lean_ctor_set(v___x_599_, 1, v___x_597_);
    lean_ctor_set(v___x_599_, 2, v___x_598_);
    lean_ctor_set(v___x_599_, 3, v_options_596_);
    v___x_600_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_600_, 0, v___x_599_);
    lean_ctor_set(v___x_600_, 1, v_msgData_590_);
    v___x_601_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_601_, 0, v___x_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___boxed(
    mut v_msgData_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_606_: *mut LeanObject = core::ptr::null_mut();
    v_res_606_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msgData_602_, v___y_603_, v___y_604_);
    lean_dec(v___y_604_);
    lean_dec_ref(v___y_603_);
    return v_res_606_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0()
-> f64 {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: f64 = 0.0;
    v___x_607_ = lean_unsigned_to_nat(0);
    v___x_608_ = lean_float_of_nat(v___x_607_);
    return v___x_608_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(
    mut v_cls_612_: *mut LeanObject,
    mut v_msg_613_: *mut LeanObject,
    mut v___y_614_: *mut LeanObject,
    mut v___y_615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_622_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v_tid_636_: u64 = 0;
    let mut v_traces_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: f64 = 0.0;
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_661_: u8 = 0;
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_617_ = lean_ctor_get(v___y_614_, 5);
                v___x_618_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msg_613_, v___y_614_, v___y_615_);
                v_a_619_ = lean_ctor_get(v___x_618_, 0);
                v_isSharedCheck_663_ = (!lean_is_exclusive(v___x_618_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v___x_621_ = v___x_618_;
                    v_isShared_622_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_619_);
                    lean_dec(v___x_618_);
                    v___x_621_ = lean_box(0);
                    v_isShared_622_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_623_ = lean_st_ref_take(v___y_615_);
                v_traceState_624_ = lean_ctor_get(v___x_623_, 4);
                v_env_625_ = lean_ctor_get(v___x_623_, 0);
                v_nextMacroScope_626_ = lean_ctor_get(v___x_623_, 1);
                v_ngen_627_ = lean_ctor_get(v___x_623_, 2);
                v_auxDeclNGen_628_ = lean_ctor_get(v___x_623_, 3);
                v_cache_629_ = lean_ctor_get(v___x_623_, 5);
                v_messages_630_ = lean_ctor_get(v___x_623_, 6);
                v_infoState_631_ = lean_ctor_get(v___x_623_, 7);
                v_snapshotTasks_632_ = lean_ctor_get(v___x_623_, 8);
                v_isSharedCheck_662_ = (!lean_is_exclusive(v___x_623_)) as u8;
                if v_isSharedCheck_662_ == 0 {
                    v___x_634_ = v___x_623_;
                    v_isShared_635_ = v_isSharedCheck_662_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_632_);
                    lean_inc(v_infoState_631_);
                    lean_inc(v_messages_630_);
                    lean_inc(v_cache_629_);
                    lean_inc(v_traceState_624_);
                    lean_inc(v_auxDeclNGen_628_);
                    lean_inc(v_ngen_627_);
                    lean_inc(v_nextMacroScope_626_);
                    lean_inc(v_env_625_);
                    lean_dec(v___x_623_);
                    v___x_634_ = lean_box(0);
                    v_isShared_635_ = v_isSharedCheck_662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_636_ = lean_ctor_get_uint64(
                    v_traceState_624_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_637_ = lean_ctor_get(v_traceState_624_, 0);
                v_isSharedCheck_661_ = (!lean_is_exclusive(v_traceState_624_)) as u8;
                if v_isSharedCheck_661_ == 0 {
                    v___x_639_ = v_traceState_624_;
                    v_isShared_640_ = v_isSharedCheck_661_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_637_);
                    lean_dec(v_traceState_624_);
                    v___x_639_ = lean_box(0);
                    v_isShared_640_ = v_isSharedCheck_661_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_641_ = lean_box(0);
                v___x_642_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0);
                v___x_643_ = 0;
                v___x_644_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1;
                v___x_645_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_645_, 0, v_cls_612_);
                lean_ctor_set(v___x_645_, 1, v___x_641_);
                lean_ctor_set(v___x_645_, 2, v___x_644_);
                lean_ctor_set_float(
                    v___x_645_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_642_,
                );
                lean_ctor_set_float(
                    v___x_645_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_642_,
                );
                lean_ctor_set_uint8(
                    v___x_645_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_643_,
                );
                v___x_646_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2;
                v___x_647_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_647_, 0, v___x_645_);
                lean_ctor_set(v___x_647_, 1, v_a_619_);
                lean_ctor_set(v___x_647_, 2, v___x_646_);
                lean_inc(v_ref_617_);
                v___x_648_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_648_, 0, v_ref_617_);
                lean_ctor_set(v___x_648_, 1, v___x_647_);
                v___x_649_ = l_Lean_PersistentArray_push___redArg(v_traces_637_, v___x_648_);
                if v_isShared_640_ == 0 {
                    lean_ctor_set(v___x_639_, 0, v___x_649_);
                    v___x_651_ = v___x_639_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_649_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_660_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_636_,
                    );
                    v___x_651_ = v_reuseFailAlloc_660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_635_ == 0 {
                    lean_ctor_set(v___x_634_, 4, v___x_651_);
                    v___x_653_ = v___x_634_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_659_, 0, v_env_625_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 1, v_nextMacroScope_626_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 2, v_ngen_627_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 3, v_auxDeclNGen_628_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 4, v___x_651_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 5, v_cache_629_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 6, v_messages_630_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 7, v_infoState_631_);
                    lean_ctor_set(v_reuseFailAlloc_659_, 8, v_snapshotTasks_632_);
                    v___x_653_ = v_reuseFailAlloc_659_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_654_ = lean_st_ref_set(v___y_615_, v___x_653_);
                v___x_655_ = lean_box(0);
                if v_isShared_622_ == 0 {
                    lean_ctor_set(v___x_621_, 0, v___x_655_);
                    v___x_657_ = v___x_621_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
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
    mut v_cls_664_: *mut LeanObject,
    mut v_msg_665_: *mut LeanObject,
    mut v___y_666_: *mut LeanObject,
    mut v___y_667_: *mut LeanObject,
    mut v___y_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_669_: *mut LeanObject = core::ptr::null_mut();
    v_res_669_ =
        l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(
            v_cls_664_, v_msg_665_, v___y_666_, v___y_667_,
        );
    lean_dec(v___y_667_);
    lean_dec_ref(v___y_666_);
    return v_res_669_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_670_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0);
    v___x_672_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_672_, 0, v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    v___x_673_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1);
    v___x_674_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_674_, 0, v___x_673_);
    lean_ctor_set(v___x_674_, 1, v___x_673_);
    return v___x_674_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9()
-> *mut LeanObject {
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_685_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
    v___x_686_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8;
    v___x_687_ = l_Lean_Name_append(v___x_686_, v___x_685_);
    return v___x_687_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11()
-> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10;
    v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
    return v___x_690_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13()
-> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12;
    v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
    return v___x_693_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(
    mut v_init_694_: *mut LeanObject,
    mut v_x_695_: *mut LeanObject,
    mut v___y_696_: *mut LeanObject,
    mut v___y_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_724_: u8 = 0;
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_735_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_739_: u8 = 0;
    let mut v_reuseFailAlloc_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_unused_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_744_: u8 = 0;
    let mut v_inheritedTraceOptions_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: u8 = 0;
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_762_: u8 = 0;
    let mut v_a_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_771_: u8 = 0;
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_695_) == 0 {
                    v_k_699_ = lean_ctor_get(v_x_695_, 1);
                    lean_inc(v_k_699_);
                    v_l_700_ = lean_ctor_get(v_x_695_, 3);
                    lean_inc(v_l_700_);
                    v_r_701_ = lean_ctor_get(v_x_695_, 4);
                    lean_inc(v_r_701_);
                    lean_dec_ref_known(v_x_695_, 5);
                    v___x_702_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_694_, v_l_700_, v___y_696_, v___y_697_);
                    if lean_obj_tag(v___x_702_) == 0 {
                        lean_dec_ref_known(v___x_702_, 1);
                        v___x_703_ = lean_st_ref_get(v___y_697_);
                        v_env_704_ = lean_ctor_get(v___x_703_, 0);
                        lean_inc_ref(v_env_704_);
                        lean_dec(v___x_703_);
                        v___x_705_ = lean_box(0);
                        v___x_706_ = l_Lean_isDeclMeta(v_env_704_, v_k_699_);
                        if v___x_706_ == 0 {
                            v___x_707_ = l_Lean_IR_findLocalDecl___redArg(v_k_699_, v___y_697_);
                            if lean_obj_tag(v___x_707_) == 0 {
                                v_a_708_ = lean_ctor_get(v___x_707_, 0);
                                lean_inc(v_a_708_);
                                lean_dec_ref_known(v___x_707_, 1);
                                if lean_obj_tag(v_a_708_) == 1 {
                                    v_val_709_ = lean_ctor_get(v_a_708_, 0);
                                    lean_inc(v_val_709_);
                                    lean_dec_ref_known(v_a_708_, 1);
                                    v_options_743_ = lean_ctor_get(v___y_696_, 2);
                                    v_hasTrace_744_ = lean_ctor_get_uint8(
                                        v_options_743_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                    );
                                    if v_hasTrace_744_ == 0 {
                                        v___y_711_ = v___y_696_;
                                        v___y_712_ = v___y_697_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_inheritedTraceOptions_745_ =
                                            lean_ctor_get(v___y_696_, 13);
                                        v___x_746_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
                                        v___x_747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
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
                                            v___x_749_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
                                            lean_inc(v_k_699_);
                                            v___x_750_ = l_Lean_MessageData_ofName(v_k_699_);
                                            v___x_751_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_751_, 0, v___x_749_);
                                            lean_ctor_set(v___x_751_, 1, v___x_750_);
                                            v___x_752_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13);
                                            v___x_753_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_753_, 0, v___x_751_);
                                            lean_ctor_set(v___x_753_, 1, v___x_752_);
                                            v___x_754_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_746_, v___x_753_, v___y_696_, v___y_697_);
                                            if lean_obj_tag(v___x_754_) == 0 {
                                                lean_dec_ref_known(v___x_754_, 1);
                                                v___y_711_ = v___y_696_;
                                                v___y_712_ = v___y_697_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec(v_val_709_);
                                                lean_dec(v_r_701_);
                                                lean_dec(v_k_699_);
                                                v_a_755_ = lean_ctor_get(v___x_754_, 0);
                                                v_isSharedCheck_762_ =
                                                    (!lean_is_exclusive(v___x_754_)) as u8;
                                                if v_isSharedCheck_762_ == 0 {
                                                    v___x_757_ = v___x_754_;
                                                    v_isShared_758_ = v_isSharedCheck_762_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_755_);
                                                    lean_dec(v___x_754_);
                                                    v___x_757_ = lean_box(0);
                                                    v_isShared_758_ = v_isSharedCheck_762_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_708_);
                                    lean_dec(v_k_699_);
                                    v_init_694_ = v___x_705_;
                                    v_x_695_ = v_r_701_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                lean_dec(v_r_701_);
                                lean_dec(v_k_699_);
                                v_a_764_ = lean_ctor_get(v___x_707_, 0);
                                v_isSharedCheck_771_ = (!lean_is_exclusive(v___x_707_)) as u8;
                                if v_isSharedCheck_771_ == 0 {
                                    v___x_766_ = v___x_707_;
                                    v_isShared_767_ = v_isSharedCheck_771_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_764_);
                                    lean_dec(v___x_707_);
                                    v___x_766_ = lean_box(0);
                                    v_isShared_767_ = v_isSharedCheck_771_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_k_699_);
                            v_init_694_ = v___x_705_;
                            v_x_695_ = v_r_701_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_r_701_);
                        lean_dec(v_k_699_);
                        return v___x_702_;
                    }
                } else {
                    v___x_773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_773_, 0, v_init_694_);
                    v___x_774_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_774_, 0, v___x_773_);
                    return v___x_774_;
                }
            }
            1 => {
                v___x_713_ = lean_st_ref_take(v___y_712_);
                v_env_714_ = lean_ctor_get(v___x_713_, 0);
                v_nextMacroScope_715_ = lean_ctor_get(v___x_713_, 1);
                v_ngen_716_ = lean_ctor_get(v___x_713_, 2);
                v_auxDeclNGen_717_ = lean_ctor_get(v___x_713_, 3);
                v_traceState_718_ = lean_ctor_get(v___x_713_, 4);
                v_messages_719_ = lean_ctor_get(v___x_713_, 6);
                v_infoState_720_ = lean_ctor_get(v___x_713_, 7);
                v_snapshotTasks_721_ = lean_ctor_get(v___x_713_, 8);
                v_isSharedCheck_741_ = (!lean_is_exclusive(v___x_713_)) as u8;
                if v_isSharedCheck_741_ == 0 {
                    v_unused_742_ = lean_ctor_get(v___x_713_, 5);
                    lean_dec(v_unused_742_);
                    v___x_723_ = v___x_713_;
                    v_isShared_724_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_721_);
                    lean_inc(v_infoState_720_);
                    lean_inc(v_messages_719_);
                    lean_inc(v_traceState_718_);
                    lean_inc(v_auxDeclNGen_717_);
                    lean_inc(v_ngen_716_);
                    lean_inc(v_nextMacroScope_715_);
                    lean_inc(v_env_714_);
                    lean_dec(v___x_713_);
                    v___x_723_ = lean_box(0);
                    v_isShared_724_ = v_isSharedCheck_741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_725_ = l_Lean_setDeclMeta(v_env_714_, v_k_699_);
                v___x_726_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
                if v_isShared_724_ == 0 {
                    lean_ctor_set(v___x_723_, 5, v___x_726_);
                    lean_ctor_set(v___x_723_, 0, v___x_725_);
                    v___x_728_ = v___x_723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_725_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 1, v_nextMacroScope_715_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 2, v_ngen_716_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 3, v_auxDeclNGen_717_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 4, v_traceState_718_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 5, v___x_726_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 6, v_messages_719_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 7, v_infoState_720_);
                    lean_ctor_set(v_reuseFailAlloc_740_, 8, v_snapshotTasks_721_);
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
                if lean_obj_tag(v___x_730_) == 0 {
                    lean_dec_ref_known(v___x_730_, 1);
                    v_init_694_ = v___x_705_;
                    v_x_695_ = v_r_701_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_r_701_);
                    v_a_732_ = lean_ctor_get(v___x_730_, 0);
                    v_isSharedCheck_739_ = (!lean_is_exclusive(v___x_730_)) as u8;
                    if v_isSharedCheck_739_ == 0 {
                        v___x_734_ = v___x_730_;
                        v_isShared_735_ = v_isSharedCheck_739_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_732_);
                        lean_dec(v___x_730_);
                        v___x_734_ = lean_box(0);
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
                    v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
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
                    v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
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
                    v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
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
    mut v_decl_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_788_: u8 = 0;
    let mut v_unused_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_779_ =
                    l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(v_decl_775_);
                v___x_780_ = lean_box(0);
                v___x_781_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_780_, v___x_779_, v_a_776_, v_a_777_);
                if lean_obj_tag(v___x_781_) == 0 {
                    v_isSharedCheck_788_ = (!lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_788_ == 0 {
                        v_unused_789_ = lean_ctor_get(v___x_781_, 0);
                        lean_dec(v_unused_789_);
                        v___x_783_ = v___x_781_;
                        v_isShared_784_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_781_);
                        v___x_783_ = lean_box(0);
                        v_isShared_784_ = v_isSharedCheck_788_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_790_ = lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_797_ = (!lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v___x_792_ = v___x_781_;
                        v_isShared_793_ = v_isSharedCheck_797_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_790_);
                        lean_dec(v___x_781_);
                        v___x_792_ = lean_box(0);
                        v_isShared_793_ = v_isSharedCheck_797_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_784_ == 0 {
                    lean_ctor_set(v___x_783_, 0, v___x_780_);
                    v___x_786_ = v___x_783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_780_);
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
                    v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
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
    mut v_decl_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_802_: *mut LeanObject = core::ptr::null_mut();
    v_res_802_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
        v_decl_798_,
        v_a_799_,
        v_a_800_,
    );
    lean_dec(v_a_800_);
    lean_dec_ref(v_a_799_);
    return v_res_802_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(
    mut v_init_803_: *mut LeanObject,
    mut v_x_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
    mut v___y_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_803_, v_x_804_, v___y_805_, v___y_806_);
    lean_dec(v___y_806_);
    lean_dec_ref(v___y_805_);
    return v_res_808_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0;
    v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
    return v___x_811_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(
    mut v_as_812_: *mut LeanObject,
    mut v_sz_813_: usize,
    mut v_i_814_: usize,
    mut v_b_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
    mut v___y_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: usize = 0;
    let mut v___x_822_: usize = 0;
    let mut v___x_824_: u8 = 0;
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_845_: u8 = 0;
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_853_: u8 = 0;
    let mut v_unused_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v_options_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_857_: u8 = 0;
    let mut v_inheritedTraceOptions_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_824_ = lean_usize_dec_lt(v_i_814_, v_sz_813_);
                if v___x_824_ == 0 {
                    v___x_825_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_825_, 0, v_b_815_);
                    return v___x_825_;
                } else {
                    v___x_826_ = lean_st_ref_get(v___y_817_);
                    v_env_827_ = lean_ctor_get(v___x_826_, 0);
                    lean_inc_ref(v_env_827_);
                    lean_dec(v___x_826_);
                    v___x_828_ = lean_box(0);
                    v_a_829_ = lean_array_uget_borrowed(v_as_812_, v_i_814_);
                    v___x_830_ = l_Lean_IR_Decl_name(v_a_829_);
                    lean_inc(v___x_830_);
                    v___x_855_ = l_Lean_isMarkedMeta(v_env_827_, v___x_830_);
                    if v___x_855_ == 0 {
                        lean_dec(v___x_830_);
                        v_a_820_ = v___x_828_;
                        state = 1;
                        continue;
                    } else {
                        v_options_856_ = lean_ctor_get(v___y_816_, 2);
                        v_hasTrace_857_ = lean_ctor_get_uint8(
                            v_options_856_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_857_ == 0 {
                            v___y_832_ = v___y_816_;
                            v___y_833_ = v___y_817_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_858_ = lean_ctor_get(v___y_816_, 13);
                            v___x_859_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
                            v___x_860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
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
                                v___x_862_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
                                lean_inc(v___x_830_);
                                v___x_863_ = l_Lean_MessageData_ofName(v___x_830_);
                                v___x_864_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_864_, 0, v___x_862_);
                                lean_ctor_set(v___x_864_, 1, v___x_863_);
                                v___x_865_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1);
                                v___x_866_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_866_, 0, v___x_864_);
                                lean_ctor_set(v___x_866_, 1, v___x_865_);
                                v___x_867_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_859_, v___x_866_, v___y_816_, v___y_817_);
                                if lean_obj_tag(v___x_867_) == 0 {
                                    lean_dec_ref_known(v___x_867_, 1);
                                    v___y_832_ = v___y_816_;
                                    v___y_833_ = v___y_817_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v___x_830_);
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
                v_env_835_ = lean_ctor_get(v___x_834_, 0);
                v_nextMacroScope_836_ = lean_ctor_get(v___x_834_, 1);
                v_ngen_837_ = lean_ctor_get(v___x_834_, 2);
                v_auxDeclNGen_838_ = lean_ctor_get(v___x_834_, 3);
                v_traceState_839_ = lean_ctor_get(v___x_834_, 4);
                v_messages_840_ = lean_ctor_get(v___x_834_, 6);
                v_infoState_841_ = lean_ctor_get(v___x_834_, 7);
                v_snapshotTasks_842_ = lean_ctor_get(v___x_834_, 8);
                v_isSharedCheck_853_ = (!lean_is_exclusive(v___x_834_)) as u8;
                if v_isSharedCheck_853_ == 0 {
                    v_unused_854_ = lean_ctor_get(v___x_834_, 5);
                    lean_dec(v_unused_854_);
                    v___x_844_ = v___x_834_;
                    v_isShared_845_ = v_isSharedCheck_853_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_842_);
                    lean_inc(v_infoState_841_);
                    lean_inc(v_messages_840_);
                    lean_inc(v_traceState_839_);
                    lean_inc(v_auxDeclNGen_838_);
                    lean_inc(v_ngen_837_);
                    lean_inc(v_nextMacroScope_836_);
                    lean_inc(v_env_835_);
                    lean_dec(v___x_834_);
                    v___x_844_ = lean_box(0);
                    v_isShared_845_ = v_isSharedCheck_853_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_846_ = l_Lean_setDeclMeta(v_env_835_, v___x_830_);
                v___x_847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once), _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
                if v_isShared_845_ == 0 {
                    lean_ctor_set(v___x_844_, 5, v___x_847_);
                    lean_ctor_set(v___x_844_, 0, v___x_846_);
                    v___x_849_ = v___x_844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_846_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 1, v_nextMacroScope_836_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 2, v_ngen_837_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 3, v_auxDeclNGen_838_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 4, v_traceState_839_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 5, v___x_847_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 6, v_messages_840_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 7, v_infoState_841_);
                    lean_ctor_set(v_reuseFailAlloc_852_, 8, v_snapshotTasks_842_);
                    v___x_849_ = v_reuseFailAlloc_852_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_850_ = lean_st_ref_set(v___y_833_, v___x_849_);
                lean_inc(v_a_829_);
                v___x_851_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(
                    v_a_829_, v___y_832_, v___y_833_,
                );
                if lean_obj_tag(v___x_851_) == 0 {
                    lean_dec_ref_known(v___x_851_, 1);
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
    mut v_as_868_: *mut LeanObject,
    mut v_sz_869_: *mut LeanObject,
    mut v_i_870_: *mut LeanObject,
    mut v_b_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_875_: usize = 0;
    let mut v_i_boxed_876_: usize = 0;
    let mut v_res_877_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_875_ = lean_unbox_usize(v_sz_869_);
    lean_dec(v_sz_869_);
    v_i_boxed_876_ = lean_unbox_usize(v_i_870_);
    lean_dec(v_i_870_);
    v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_as_868_, v_sz_boxed_875_, v_i_boxed_876_, v_b_871_, v___y_872_, v___y_873_);
    lean_dec(v___y_873_);
    lean_dec_ref(v___y_872_);
    lean_dec_ref(v_as_868_);
    return v_res_877_;
}
pub unsafe fn l_Lean_IR_inferMeta(
    mut v_decls_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isModule_885_: u8 = 0;
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_889_: usize = 0;
    let mut v___x_890_: usize = 0;
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_894_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut v_unused_899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_882_ = lean_st_ref_get(v_a_880_);
                v_env_883_ = lean_ctor_get(v___x_882_, 0);
                lean_inc_ref(v_env_883_);
                lean_dec(v___x_882_);
                v___x_884_ = l_Lean_Environment_header(v_env_883_);
                lean_dec_ref(v_env_883_);
                v_isModule_885_ = lean_ctor_get_uint8(
                    v___x_884_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 4) as u32,
                );
                lean_dec_ref(v___x_884_);
                if v_isModule_885_ == 0 {
                    v___x_886_ = lean_box(0);
                    v___x_887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_887_, 0, v___x_886_);
                    return v___x_887_;
                } else {
                    v___x_888_ = lean_box(0);
                    v_sz_889_ = lean_array_size(v_decls_878_);
                    v___x_890_ = 0usize;
                    v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_decls_878_, v_sz_889_, v___x_890_, v___x_888_, v_a_879_, v_a_880_);
                    if lean_obj_tag(v___x_891_) == 0 {
                        v_isSharedCheck_898_ = (!lean_is_exclusive(v___x_891_)) as u8;
                        if v_isSharedCheck_898_ == 0 {
                            v_unused_899_ = lean_ctor_get(v___x_891_, 0);
                            lean_dec(v_unused_899_);
                            v___x_893_ = v___x_891_;
                            v_isShared_894_ = v_isSharedCheck_898_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_891_);
                            v___x_893_ = lean_box(0);
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
                    lean_ctor_set(v___x_893_, 0, v___x_888_);
                    v___x_896_ = v___x_893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_888_);
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
    mut v_decls_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_IR_inferMeta(v_decls_900_, v_a_901_, v_a_902_);
    lean_dec(v_a_902_);
    lean_dec_ref(v_a_901_);
    lean_dec_ref(v_decls_900_);
    return v_res_904_;
}
pub unsafe fn lean_eval_check_meta(
    mut v_env_909_: *mut LeanObject,
    mut v_declName_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_911_: u8 = 0;
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: u8 = 0;
    lean_inc(v_declName_910_);
    v___x_911_ = l_Lean_getIRPhases(v_env_909_, v_declName_910_);
    v___x_912_ = 0;
    v___x_913_ = l_Lean_instBEqIRPhases_beq(v___x_911_, v___x_912_);
    if v___x_913_ == 0 {
        let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_declName_910_);
        v___x_914_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0;
        return v___x_914_;
    } else {
        let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        v___x_915_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1;
        v___x_916_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_declName_910_,
            v___x_913_,
        );
        v___x_917_ = lean_string_append(v___x_915_, v___x_916_);
        lean_dec_ref(v___x_916_);
        v___x_918_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2;
        v___x_919_ = lean_string_append(v___x_917_, v___x_918_);
        v___x_920_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_920_, 0, v___x_919_);
        return v___x_920_;
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    v___x_970_ = lean_unsigned_to_nat(3167601923);
    v___x_971_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_972_ = l_Lean_Name_num___override(v___x_971_, v___x_970_);
    return v___x_972_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    v___x_974_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_975_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_976_ = l_Lean_Name_str___override(v___x_975_, v___x_974_);
    return v___x_976_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    v___x_978_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
    v___x_979_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_980_ = l_Lean_Name_str___override(v___x_979_, v___x_978_);
    return v___x_980_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = lean_unsigned_to_nat(2);
    v___x_982_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_983_ = l_Lean_Name_num___override(v___x_982_, v___x_981_);
    return v___x_983_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6;
    v___x_986_ = 0;
    v___x_987_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
    v___x_988_ = l_Lean_registerTraceClass(v___x_985_, v___x_986_, v___x_987_);
    return v___x_988_;
}
pub unsafe fn l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(
    mut v_a_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_res_990_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
    return v_res_990_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Meta(builtin);
}
