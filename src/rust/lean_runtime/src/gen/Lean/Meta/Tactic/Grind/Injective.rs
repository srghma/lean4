// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injective
// Imports: Lean.Meta.Tactic.Grind.EMatchTheorem Init.Data.Function Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_empty, l_Lean_NameSet_insert};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_levelParams;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_eta, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_sort___override,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux;
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
    l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Theorems::l_Lean_Meta_Grind_getProofForDecl;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::l_Lean_ScopedEnvExtension_addCore___redArg;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,1891887995088964530 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,622053547050603573 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,7466587695041019504 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,12476371541004604745 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,17132214338911791756 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,1550241582563015600 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,12168955777775944890 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,4539651995539963167 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,6727391452282951466 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15194044346522623659 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,7456218402816208931 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15292532237123326354 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,6345104771979739696 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,14920283104170040409 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,1891887995088964530 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject,16986677381411493332 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,((( 1215188614 as usize) << 1) | 1) as *mut LeanObject,3751231088157539844 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,8081854262743651883 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15920477089225671659 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,8453999917361367102 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,14562555973890958749 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value: LeanStringObject<97> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 105, 110, 106, 101, 99, 116, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 117, 115, 101, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 115, 121, 109, 98, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value: LeanStringObject<78> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 116, 104, 101, 111, 114, 101, 109, 32, 104, 97, 115, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115, 44, 32, 98, 117, 116, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value) as *mut LeanObject,920240211420121313 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut LeanObject,14487767036850709044 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 70, 117, 110, 99, 116, 105, 111, 110, 46, 73, 110, 106, 101, 99, 116, 105, 118, 101, 32, 60, 102, 117, 110, 62, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1341_ = lean_unsigned_to_nat(3173337487);
    v___x_1342_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1343_ = l_Lean_Name_num___override(v___x_1342_, v___x_1341_);
    return v___x_1343_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1346_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1347_ = l_Lean_Name_str___override(v___x_1346_, v___x_1345_);
    return v___x_1347_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1350_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1351_ = l_Lean_Name_str___override(v___x_1350_, v___x_1349_);
    return v___x_1351_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1352_ = lean_unsigned_to_nat(2);
    v___x_1353_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1354_ = l_Lean_Name_num___override(v___x_1353_, v___x_1352_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1357_ = 0;
    v___x_1358_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1359_ = l_Lean_registerTraceClass(v___x_1356_, v___x_1357_, v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2____boxed(
    mut v_a_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_res_1361_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
    return v_res_1361_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_;
    v___x_1381_ = 0;
    v___x_1382_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_;
    v___x_1383_ = l_Lean_registerTraceClass(v___x_1380_, v___x_1381_, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2____boxed(
    mut v_a_1384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1385_: *mut LeanObject = core::ptr::null_mut();
    v_res_1385_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
    return v_res_1385_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1391_ = lean_unsigned_to_nat(3941467707);
    v___x_1392_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1393_ = l_Lean_Name_num___override(v___x_1392_, v___x_1391_);
    return v___x_1393_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1395_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1396_ = l_Lean_Name_str___override(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1397_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1398_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1399_ = l_Lean_Name_str___override(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1400_ = lean_unsigned_to_nat(2);
    v___x_1401_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1402_ = l_Lean_Name_num___override(v___x_1401_, v___x_1400_);
    return v___x_1402_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
    v___x_1405_ = 0;
    v___x_1406_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1407_ = l_Lean_registerTraceClass(v___x_1404_, v___x_1405_, v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2____boxed(
    mut v_a_1408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1409_: *mut LeanObject = core::ptr::null_mut();
    v_res_1409_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
    return v_res_1409_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0()
-> *mut LeanObject {
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1411_: *mut LeanObject = core::ptr::null_mut();
    v___x_1410_ = lean_box(0);
    v_dummy_1411_ = l_Lean_Expr_sort___override(v___x_1410_);
    return v_dummy_1411_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(
    mut v_upperBound_1412_: *mut LeanObject,
    mut v_args_1413_: *mut LeanObject,
    mut v_a_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
    mut v_b_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1428_ = lean_nat_dec_lt(v_a_1415_, v_upperBound_1412_);
                if v___x_1428_ == 0 {
                    lean_dec(v_a_1415_);
                    v___x_1429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1429_, 0, v_b_1416_);
                    return v___x_1429_;
                } else {
                    v___x_1430_ = lean_box(0);
                    v___x_1431_ = lean_array_fget_borrowed(v_args_1413_, v_a_1415_);
                    v___x_1434_ = lean_array_get_size(v_a_1414_);
                    v___x_1435_ = lean_nat_dec_lt(v_a_1415_, v___x_1434_);
                    if v___x_1435_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1436_ = lean_array_fget_borrowed(v_a_1414_, v_a_1415_);
                        v___x_1437_ = (lean_unbox(v___x_1436_) as u8);
                        match v___x_1437_ {
                            0 => {
                                state = 2;
                                continue;
                            }
                            3 => {
                                state = 2;
                                continue;
                            }
                            _ => {
                                v_a_1424_ = v___x_1430_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1425_ = lean_unsigned_to_nat(1);
                v___x_1426_ = lean_nat_add(v_a_1415_, v___x_1425_);
                lean_dec(v_a_1415_);
                v_a_1415_ = v___x_1426_;
                v_b_1416_ = v_a_1424_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___x_1431_);
                v___x_1433_ =
                    l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(
                        v___x_1431_,
                        v___y_1417_,
                        v___y_1418_,
                        v___y_1419_,
                        v___y_1420_,
                        v___y_1421_,
                    );
                if lean_obj_tag(v___x_1433_) == 0 {
                    lean_dec_ref_known(v___x_1433_, 1);
                    v_a_1424_ = v___x_1430_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_a_1415_);
                    return v___x_1433_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(
    mut v_x_1438_: *mut LeanObject,
    mut v_x_1439_: *mut LeanObject,
    mut v_x_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_fn_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1438_) == 5 {
                    v_fn_1475_ = lean_ctor_get(v_x_1438_, 0);
                    lean_inc_ref(v_fn_1475_);
                    v_arg_1476_ = lean_ctor_get(v_x_1438_, 1);
                    lean_inc_ref(v_arg_1476_);
                    lean_dec_ref_known(v_x_1438_, 2);
                    v___x_1477_ = lean_array_set(v_x_1439_, v_x_1440_, v_arg_1476_);
                    v___x_1478_ = lean_unsigned_to_nat(1);
                    v___x_1479_ = lean_nat_sub(v_x_1440_, v___x_1478_);
                    lean_dec(v_x_1440_);
                    v_x_1438_ = v_fn_1475_;
                    v_x_1439_ = v___x_1477_;
                    v_x_1440_ = v___x_1479_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_1440_);
                    if lean_obj_tag(v_x_1438_) == 4 {
                        v_declName_1481_ = lean_ctor_get(v_x_1438_, 0);
                        v___x_1482_ = lean_st_ref_take(v___y_1441_);
                        lean_inc(v_declName_1481_);
                        v___x_1483_ = l_Lean_NameSet_insert(v___x_1482_, v_declName_1481_);
                        v___x_1484_ = lean_st_ref_set(v___y_1441_, v___x_1483_);
                        v___y_1448_ = v___y_1441_;
                        v___y_1449_ = v___y_1442_;
                        v___y_1450_ = v___y_1443_;
                        v___y_1451_ = v___y_1444_;
                        v___y_1452_ = v___y_1445_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1448_ = v___y_1441_;
                        v___y_1449_ = v___y_1442_;
                        v___y_1450_ = v___y_1443_;
                        v___y_1451_ = v___y_1444_;
                        v___y_1452_ = v___y_1445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1453_ = lean_array_get_size(v_x_1439_);
                v___x_1454_ = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(
                    v_x_1438_,
                    v___x_1453_,
                    v___y_1449_,
                    v___y_1450_,
                    v___y_1451_,
                    v___y_1452_,
                );
                if lean_obj_tag(v___x_1454_) == 0 {
                    v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
                    lean_inc(v_a_1455_);
                    lean_dec_ref_known(v___x_1454_, 1);
                    v___x_1456_ = lean_unsigned_to_nat(0);
                    v___x_1457_ = lean_box(0);
                    v___x_1458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v___x_1453_, v_x_1439_, v_a_1455_, v___x_1456_, v___x_1457_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
                    lean_dec(v_a_1455_);
                    lean_dec_ref(v_x_1439_);
                    if lean_obj_tag(v___x_1458_) == 0 {
                        v_isSharedCheck_1465_ = (!lean_is_exclusive(v___x_1458_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = lean_ctor_get(v___x_1458_, 0);
                            lean_dec(v_unused_1466_);
                            v___x_1460_ = v___x_1458_;
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1458_);
                            v___x_1460_ = lean_box(0);
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1458_;
                    }
                } else {
                    lean_dec_ref(v_x_1439_);
                    v_a_1467_ = lean_ctor_get(v___x_1454_, 0);
                    v_isSharedCheck_1474_ = (!lean_is_exclusive(v___x_1454_)) as u8;
                    if v_isSharedCheck_1474_ == 0 {
                        v___x_1469_ = v___x_1454_;
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1467_);
                        lean_dec(v___x_1454_);
                        v___x_1469_ = lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1461_ == 0 {
                    lean_ctor_set(v___x_1460_, 0, v___x_1457_);
                    v___x_1463_ = v___x_1460_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1457_);
                    v___x_1463_ = v_reuseFailAlloc_1464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1463_;
            }
            4 => {
                if v_isShared_1470_ == 0 {
                    v___x_1472_ = v___x_1469_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
                    v___x_1472_ = v_reuseFailAlloc_1473_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(
    mut v_e_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
    mut v_a_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: u8 = 0;
    v___x_1492_ = l_Lean_Expr_isApp(v_e_1485_);
    if v___x_1492_ == 0 {
        let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_1485_);
        v___x_1493_ = lean_box(0);
        v___x_1494_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1494_, 0, v___x_1493_);
        return v___x_1494_;
    } else {
        let mut v_dummy_1495_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nargs_1496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
        v_dummy_1495_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0);
        v_nargs_1496_ = l_Lean_Expr_getAppNumArgs(v_e_1485_);
        lean_inc(v_nargs_1496_);
        v___x_1497_ = lean_mk_array(v_nargs_1496_, v_dummy_1495_);
        v___x_1498_ = lean_unsigned_to_nat(1);
        v___x_1499_ = lean_nat_sub(v_nargs_1496_, v___x_1498_);
        lean_dec(v_nargs_1496_);
        v___x_1500_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_e_1485_, v___x_1497_, v___x_1499_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
        return v___x_1500_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___boxed(
    mut v_e_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
    mut v_a_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(
        v_e_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_,
    );
    lean_dec(v_a_1506_);
    lean_dec_ref(v_a_1505_);
    lean_dec(v_a_1504_);
    lean_dec_ref(v_a_1503_);
    lean_dec(v_a_1502_);
    return v_res_1508_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg___boxed(
    mut v_upperBound_1509_: *mut LeanObject,
    mut v_args_1510_: *mut LeanObject,
    mut v_a_1511_: *mut LeanObject,
    mut v_a_1512_: *mut LeanObject,
    mut v_b_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
    mut v___y_1516_: *mut LeanObject,
    mut v___y_1517_: *mut LeanObject,
    mut v___y_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1520_: *mut LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_1509_, v_args_1510_, v_a_1511_, v_a_1512_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
    lean_dec(v___y_1518_);
    lean_dec_ref(v___y_1517_);
    lean_dec(v___y_1516_);
    lean_dec_ref(v___y_1515_);
    lean_dec(v___y_1514_);
    lean_dec_ref(v_a_1511_);
    lean_dec_ref(v_args_1510_);
    lean_dec(v_upperBound_1509_);
    return v_res_1520_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1___boxed(
    mut v_x_1521_: *mut LeanObject,
    mut v_x_1522_: *mut LeanObject,
    mut v_x_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
    mut v___y_1526_: *mut LeanObject,
    mut v___y_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_x_1521_, v_x_1522_, v_x_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
    lean_dec(v___y_1528_);
    lean_dec_ref(v___y_1527_);
    lean_dec(v___y_1526_);
    lean_dec_ref(v___y_1525_);
    lean_dec(v___y_1524_);
    return v_res_1530_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(
    mut v_upperBound_1531_: *mut LeanObject,
    mut v_args_1532_: *mut LeanObject,
    mut v_a_1533_: *mut LeanObject,
    mut v_inst_1534_: *mut LeanObject,
    mut v_R_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_b_1537_: *mut LeanObject,
    mut v_c_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
    mut v___y_1542_: *mut LeanObject,
    mut v___y_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_1531_, v_args_1532_, v_a_1533_, v_a_1536_, v_b_1537_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
    return v___x_1545_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___boxed(
    mut v_upperBound_1546_: *mut LeanObject,
    mut v_args_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_inst_1549_: *mut LeanObject,
    mut v_R_1550_: *mut LeanObject,
    mut v_a_1551_: *mut LeanObject,
    mut v_b_1552_: *mut LeanObject,
    mut v_c_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
    mut v___y_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(v_upperBound_1546_, v_args_1547_, v_a_1548_, v_inst_1549_, v_R_1550_, v_a_1551_, v_b_1552_, v_c_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
    lean_dec(v___y_1558_);
    lean_dec_ref(v___y_1557_);
    lean_dec(v___y_1556_);
    lean_dec_ref(v___y_1555_);
    lean_dec(v___y_1554_);
    lean_dec_ref(v_a_1548_);
    lean_dec_ref(v_args_1547_);
    lean_dec(v_upperBound_1546_);
    return v_res_1560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(
    mut v_f_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_unused_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_f_1561_) == 4 {
                    v_declName_1567_ = lean_ctor_get(v_f_1561_, 0);
                    lean_inc(v_declName_1567_);
                    lean_dec_ref_known(v_f_1561_, 2);
                    v___x_1568_ = l_Lean_NameSet_empty;
                    v___x_1569_ = l_Lean_NameSet_insert(v___x_1568_, v_declName_1567_);
                    v___x_1570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1570_, 0, v___x_1569_);
                    return v___x_1570_;
                } else {
                    v___x_1571_ = l_Lean_NameSet_empty;
                    v___x_1572_ = lean_st_mk_ref(v___x_1571_);
                    v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(v_f_1561_, v___x_1572_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
                    if lean_obj_tag(v___x_1573_) == 0 {
                        v_isSharedCheck_1581_ = (!lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v_unused_1582_ = lean_ctor_get(v___x_1573_, 0);
                            lean_dec(v_unused_1582_);
                            v___x_1575_ = v___x_1573_;
                            v_isShared_1576_ = v_isSharedCheck_1581_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1573_);
                            v___x_1575_ = lean_box(0);
                            v_isShared_1576_ = v_isSharedCheck_1581_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1572_);
                        v_a_1583_ = lean_ctor_get(v___x_1573_, 0);
                        v_isSharedCheck_1590_ = (!lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1585_ = v___x_1573_;
                            v_isShared_1586_ = v_isSharedCheck_1590_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1583_);
                            lean_dec(v___x_1573_);
                            v___x_1585_ = lean_box(0);
                            v_isShared_1586_ = v_isSharedCheck_1590_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1577_ = lean_st_ref_get(v___x_1572_);
                lean_dec(v___x_1572_);
                if v_isShared_1576_ == 0 {
                    lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1579_;
            }
            3 => {
                if v_isShared_1586_ == 0 {
                    v___x_1588_ = v___x_1585_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames___boxed(
    mut v_f_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
    mut v_a_1593_: *mut LeanObject,
    mut v_a_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1597_: *mut LeanObject = core::ptr::null_mut();
    v_res_1597_ =
        l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(
            v_f_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_,
        );
    lean_dec(v_a_1595_);
    lean_dec_ref(v_a_1594_);
    lean_dec(v_a_1593_);
    lean_dec_ref(v_a_1592_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(
    mut v_k_1598_: *mut LeanObject,
    mut v_b_1599_: *mut LeanObject,
    mut v_c_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1604_);
    lean_inc_ref(v___y_1603_);
    lean_inc(v___y_1602_);
    lean_inc_ref(v___y_1601_);
    v___x_1606_ = lean_apply_7(
        v_k_1598_,
        v_b_1599_,
        v_c_1600_,
        v___y_1601_,
        v___y_1602_,
        v___y_1603_,
        v___y_1604_,
        lean_box(0),
    );
    return v___x_1606_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed(
    mut v_k_1607_: *mut LeanObject,
    mut v_b_1608_: *mut LeanObject,
    mut v_c_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1615_: *mut LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(v_k_1607_, v_b_1608_, v_c_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
    lean_dec(v___y_1613_);
    lean_dec_ref(v___y_1612_);
    lean_dec(v___y_1611_);
    lean_dec_ref(v___y_1610_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(
    mut v_type_1616_: *mut LeanObject,
    mut v_k_1617_: *mut LeanObject,
    mut v_cleanupAnnotations_1618_: u8,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1624_ = lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1624_, 0, v_k_1617_);
                v___x_1625_ = 0;
                v___x_1626_ = lean_box(0);
                v___x_1627_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_1625_,
                        v___x_1626_,
                        v_type_1616_,
                        v___f_1624_,
                        v_cleanupAnnotations_1618_,
                        v___x_1625_,
                        v___y_1619_,
                        v___y_1620_,
                        v___y_1621_,
                        v___y_1622_,
                    );
                if lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1635_ = (!lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1630_ = v___x_1627_;
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1628_);
                        lean_dec(v___x_1627_);
                        v___x_1630_ = lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1643_ = (!lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v___x_1638_ = v___x_1627_;
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1636_);
                        lean_dec(v___x_1627_);
                        v___x_1638_ = lean_box(0);
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1631_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1633_;
            }
            3 => {
                if v_isShared_1639_ == 0 {
                    v___x_1641_ = v___x_1638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___boxed(
    mut v_type_1644_: *mut LeanObject,
    mut v_k_1645_: *mut LeanObject,
    mut v_cleanupAnnotations_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1652_: u8 = 0;
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1652_ = (lean_unbox(v_cleanupAnnotations_1646_) as u8);
    v_res_1653_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_1644_, v_k_1645_, v_cleanupAnnotations_boxed_1652_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
    lean_dec(v___y_1650_);
    lean_dec_ref(v___y_1649_);
    lean_dec(v___y_1648_);
    lean_dec_ref(v___y_1647_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(
    mut v_00_u03b1_1654_: *mut LeanObject,
    mut v_type_1655_: *mut LeanObject,
    mut v_k_1656_: *mut LeanObject,
    mut v_cleanupAnnotations_1657_: u8,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_1655_, v_k_1656_, v_cleanupAnnotations_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___boxed(
    mut v_00_u03b1_1664_: *mut LeanObject,
    mut v_type_1665_: *mut LeanObject,
    mut v_k_1666_: *mut LeanObject,
    mut v_cleanupAnnotations_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1673_: u8 = 0;
    let mut v_res_1674_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1673_ = (lean_unbox(v_cleanupAnnotations_1667_) as u8);
    v_res_1674_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(v_00_u03b1_1664_, v_type_1665_, v_k_1666_, v_cleanupAnnotations_boxed_1673_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
    lean_dec(v___y_1671_);
    lean_dec_ref(v___y_1670_);
    lean_dec(v___y_1669_);
    lean_dec_ref(v___y_1668_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(
    mut v_msgData_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1681_ = lean_st_ref_get(v___y_1679_);
    v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
    lean_inc_ref(v_env_1682_);
    lean_dec(v___x_1681_);
    v___x_1683_ = lean_st_ref_get(v___y_1677_);
    v_mctx_1684_ = lean_ctor_get(v___x_1683_, 0);
    lean_inc_ref(v_mctx_1684_);
    lean_dec(v___x_1683_);
    v_lctx_1685_ = lean_ctor_get(v___y_1676_, 2);
    v_options_1686_ = lean_ctor_get(v___y_1678_, 2);
    lean_inc_ref(v_options_1686_);
    lean_inc_ref(v_lctx_1685_);
    v___x_1687_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1687_, 0, v_env_1682_);
    lean_ctor_set(v___x_1687_, 1, v_mctx_1684_);
    lean_ctor_set(v___x_1687_, 2, v_lctx_1685_);
    lean_ctor_set(v___x_1687_, 3, v_options_1686_);
    v___x_1688_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1688_, 0, v___x_1687_);
    lean_ctor_set(v___x_1688_, 1, v_msgData_1675_);
    v___x_1689_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2___boxed(
    mut v_msgData_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msgData_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    lean_dec(v___y_1694_);
    lean_dec_ref(v___y_1693_);
    lean_dec(v___y_1692_);
    lean_dec_ref(v___y_1691_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(
    mut v_msg_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1703_ = lean_ctor_get(v___y_1700_, 5);
                v___x_1704_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
                v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
                v_isSharedCheck_1713_ = (!lean_is_exclusive(v___x_1704_)) as u8;
                if v_isSharedCheck_1713_ == 0 {
                    v___x_1707_ = v___x_1704_;
                    v_isShared_1708_ = v_isSharedCheck_1713_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1705_);
                    lean_dec(v___x_1704_);
                    v___x_1707_ = lean_box(0);
                    v_isShared_1708_ = v_isSharedCheck_1713_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1703_);
                v___x_1709_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1709_, 0, v_ref_1703_);
                lean_ctor_set(v___x_1709_, 1, v_a_1705_);
                if v_isShared_1708_ == 0 {
                    lean_ctor_set_tag(v___x_1707_, 1);
                    lean_ctor_set(v___x_1707_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1712_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg___boxed(
    mut v_msg_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    lean_dec(v___y_1718_);
    lean_dec_ref(v___y_1717_);
    lean_dec(v___y_1716_);
    lean_dec_ref(v___y_1715_);
    return v_res_1720_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(
    mut v_init_1721_: *mut LeanObject,
    mut v_x_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1722_) == 0 {
                    v_k_1723_ = lean_ctor_get(v_x_1722_, 1);
                    v_l_1724_ = lean_ctor_get(v_x_1722_, 3);
                    v_r_1725_ = lean_ctor_get(v_x_1722_, 4);
                    v___x_1726_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_1721_, v_r_1725_);
                    lean_inc(v_k_1723_);
                    v___x_1727_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1727_, 0, v_k_1723_);
                    lean_ctor_set(v___x_1727_, 1, v___x_1726_);
                    v_init_1721_ = v___x_1727_;
                    v_x_1722_ = v_l_1724_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1721_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0___boxed(
    mut v_init_1729_: *mut LeanObject,
    mut v_x_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1731_: *mut LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_1729_, v_x_1730_);
    lean_dec(v_x_1730_);
    return v_res_1731_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(
    mut v_a_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1732_) == 0 {
                    v___x_1734_ = l_List_reverse___redArg(v_a_1733_);
                    return v___x_1734_;
                } else {
                    v_head_1735_ = lean_ctor_get(v_a_1732_, 0);
                    v_tail_1736_ = lean_ctor_get(v_a_1732_, 1);
                    v_isSharedCheck_1745_ = (!lean_is_exclusive(v_a_1732_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1738_ = v_a_1732_;
                        v_isShared_1739_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1736_);
                        lean_inc(v_head_1735_);
                        lean_dec(v_a_1732_);
                        v___x_1738_ = lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1740_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_1740_, 0, v_head_1735_);
                if v_isShared_1739_ == 0 {
                    lean_ctor_set(v___x_1738_, 1, v_a_1733_);
                    lean_ctor_set(v___x_1738_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1740_);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1733_);
                    v___x_1742_ = v_reuseFailAlloc_1744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1732_ = v_tail_1736_;
                v_a_1733_ = v___x_1742_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1747_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0;
    v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1750_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2;
    v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6;
    v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(
    mut v_hasUniverses_1759_: u8,
    mut v_xs_1760_: *mut LeanObject,
    mut v_type_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v___y_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5;
                v___x_1825_ = lean_unsigned_to_nat(3);
                v___x_1826_ = l_Lean_Expr_isAppOfArity(v_type_1761_, v___x_1824_, v___x_1825_);
                if v___x_1826_ == 0 {
                    v___x_1827_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7);
                    v___x_1828_ = l_Lean_indentExpr(v_type_1761_);
                    v___x_1829_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1829_, 0, v___x_1827_);
                    lean_ctor_set(v___x_1829_, 1, v___x_1828_);
                    v___x_1830_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1829_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
                    v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
                    v_isSharedCheck_1838_ = (!lean_is_exclusive(v___x_1830_)) as u8;
                    if v_isSharedCheck_1838_ == 0 {
                        v___x_1833_ = v___x_1830_;
                        v_isShared_1834_ = v_isSharedCheck_1838_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_1831_);
                        lean_dec(v___x_1830_);
                        v___x_1833_ = lean_box(0);
                        v_isShared_1834_ = v_isSharedCheck_1838_;
                        state = 11;
                        continue;
                    }
                } else {
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1769_ = lean_box(0);
                v___x_1770_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v___x_1769_, v___y_1768_);
                lean_dec(v___y_1768_);
                v___x_1771_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(v___x_1770_, v___x_1769_);
                v___x_1772_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                return v___x_1772_;
            }
            2 => {
                v___x_1778_ = l_Lean_Expr_appArg_x21(v_type_1761_);
                lean_dec_ref(v_type_1761_);
                v___x_1779_ = l_Lean_Expr_eta(v___x_1778_);
                lean_inc_ref(v___x_1779_);
                v___x_1780_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(v___x_1779_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
                if lean_obj_tag(v___x_1780_) == 0 {
                    v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
                    lean_inc(v_a_1781_);
                    lean_dec_ref_known(v___x_1780_, 1);
                    if lean_obj_tag(v_a_1781_) == 0 {
                        lean_dec_ref(v___x_1779_);
                        v___y_1768_ = v_a_1781_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1782_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1);
                        v___x_1783_ = l_Lean_indentExpr(v___x_1779_);
                        v___x_1784_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1784_, 0, v___x_1782_);
                        lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                        v___x_1785_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1784_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
                        v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
                        v_isSharedCheck_1793_ = (!lean_is_exclusive(v___x_1785_)) as u8;
                        if v_isSharedCheck_1793_ == 0 {
                            v___x_1788_ = v___x_1785_;
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1786_);
                            lean_dec(v___x_1785_);
                            v___x_1788_ = lean_box(0);
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1779_);
                    v_a_1794_ = lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1801_ = (!lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1780_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1794_);
                        lean_dec(v___x_1780_);
                        v___x_1796_ = lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1789_ == 0 {
                    v___x_1791_ = v___x_1788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
                    v___x_1791_ = v_reuseFailAlloc_1792_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1791_;
            }
            5 => {
                if v_isShared_1797_ == 0 {
                    v___x_1799_ = v___x_1796_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1799_;
            }
            7 => {
                if v___y_1807_ == 0 {
                    v___y_1774_ = v___y_1805_;
                    v___y_1775_ = v___y_1804_;
                    v___y_1776_ = v___y_1803_;
                    v___y_1777_ = v___y_1806_;
                    state = 2;
                    continue;
                } else {
                    v___x_1808_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3);
                    v___x_1809_ = l_Lean_indentExpr(v_type_1761_);
                    v___x_1810_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1810_, 0, v___x_1808_);
                    lean_ctor_set(v___x_1810_, 1, v___x_1809_);
                    v___x_1811_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1810_, v___y_1805_, v___y_1804_, v___y_1803_, v___y_1806_);
                    v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
                    v_isSharedCheck_1819_ = (!lean_is_exclusive(v___x_1811_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1814_ = v___x_1811_;
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1812_);
                        lean_dec(v___x_1811_);
                        v___x_1814_ = lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_1815_ == 0 {
                    v___x_1817_ = v___x_1814_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
                    v___x_1817_ = v_reuseFailAlloc_1818_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1817_;
            }
            10 => {
                v___x_1821_ = lean_array_get_size(v_xs_1760_);
                v___x_1822_ = lean_unsigned_to_nat(0);
                v___x_1823_ = lean_nat_dec_eq(v___x_1821_, v___x_1822_);
                if v___x_1823_ == 0 {
                    v___y_1803_ = v___y_1764_;
                    v___y_1804_ = v___y_1763_;
                    v___y_1805_ = v___y_1762_;
                    v___y_1806_ = v___y_1765_;
                    v___y_1807_ = v___x_1823_;
                    state = 7;
                    continue;
                } else {
                    v___y_1803_ = v___y_1764_;
                    v___y_1804_ = v___y_1763_;
                    v___y_1805_ = v___y_1762_;
                    v___y_1806_ = v___y_1765_;
                    v___y_1807_ = v_hasUniverses_1759_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                if v_isShared_1834_ == 0 {
                    v___x_1836_ = v___x_1833_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
                    v___x_1836_ = v_reuseFailAlloc_1837_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed(
    mut v_hasUniverses_1839_: *mut LeanObject,
    mut v_xs_1840_: *mut LeanObject,
    mut v_type_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasUniverses_boxed_1847_: u8 = 0;
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_hasUniverses_boxed_1847_ = (lean_unbox(v_hasUniverses_1839_) as u8);
    v_res_1848_ =
        l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(
            v_hasUniverses_boxed_1847_,
            v_xs_1840_,
            v_type_1841_,
            v___y_1842_,
            v___y_1843_,
            v___y_1844_,
            v___y_1845_,
        );
    lean_dec(v___y_1845_);
    lean_dec_ref(v___y_1844_);
    lean_dec(v___y_1843_);
    lean_dec_ref(v___y_1842_);
    lean_dec_ref(v_xs_1840_);
    return v_res_1848_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
    mut v_proof_1849_: *mut LeanObject,
    mut v_hasUniverses_1850_: u8,
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1854_);
                lean_inc_ref(v_a_1853_);
                lean_inc(v_a_1852_);
                lean_inc_ref(v_a_1851_);
                v___x_1856_ =
                    lean_infer_type(v_proof_1849_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                if lean_obj_tag(v___x_1856_) == 0 {
                    v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
                    lean_inc(v_a_1857_);
                    lean_dec_ref_known(v___x_1856_, 1);
                    v___x_1858_ = lean_box((v_hasUniverses_1850_) as usize);
                    v___f_1859_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    lean_closure_set(v___f_1859_, 0, v___x_1858_);
                    v___x_1860_ = 0;
                    v___x_1861_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_a_1857_, v___f_1859_, v___x_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                    return v___x_1861_;
                } else {
                    v_a_1862_ = lean_ctor_get(v___x_1856_, 0);
                    v_isSharedCheck_1869_ = (!lean_is_exclusive(v___x_1856_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1864_ = v___x_1856_;
                        v_isShared_1865_ = v_isSharedCheck_1869_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1862_);
                        lean_dec(v___x_1856_);
                        v___x_1864_ = lean_box(0);
                        v_isShared_1865_ = v_isSharedCheck_1869_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1865_ == 0 {
                    v___x_1867_ = v___x_1864_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___boxed(
    mut v_proof_1870_: *mut LeanObject,
    mut v_hasUniverses_1871_: *mut LeanObject,
    mut v_a_1872_: *mut LeanObject,
    mut v_a_1873_: *mut LeanObject,
    mut v_a_1874_: *mut LeanObject,
    mut v_a_1875_: *mut LeanObject,
    mut v_a_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hasUniverses_boxed_1877_: u8 = 0;
    let mut v_res_1878_: *mut LeanObject = core::ptr::null_mut();
    v_hasUniverses_boxed_1877_ = (lean_unbox(v_hasUniverses_1871_) as u8);
    v_res_1878_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
        v_proof_1870_,
        v_hasUniverses_boxed_1877_,
        v_a_1872_,
        v_a_1873_,
        v_a_1874_,
        v_a_1875_,
    );
    lean_dec(v_a_1875_);
    lean_dec_ref(v_a_1874_);
    lean_dec(v_a_1873_);
    lean_dec_ref(v_a_1872_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(
    mut v_00_u03b1_1879_: *mut LeanObject,
    mut v_msg_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    v___x_1886_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    return v___x_1886_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___boxed(
    mut v_00_u03b1_1887_: *mut LeanObject,
    mut v_msg_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1894_: *mut LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(v_00_u03b1_1887_, v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
    lean_dec(v___y_1892_);
    lean_dec_ref(v___y_1891_);
    lean_dec(v___y_1890_);
    lean_dec_ref(v___y_1889_);
    return v_res_1894_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___y_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constName_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1895_) == 0 {
                    v___x_1897_ = l_List_reverse___redArg(v_a_1896_);
                    return v___x_1897_;
                } else {
                    v_head_1898_ = lean_ctor_get(v_a_1895_, 0);
                    v_tail_1899_ = lean_ctor_get(v_a_1895_, 1);
                    v_isSharedCheck_1911_ = (!lean_is_exclusive(v_a_1895_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1901_ = v_a_1895_;
                        v_isShared_1902_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1899_);
                        lean_inc(v_head_1898_);
                        lean_dec(v_a_1895_);
                        v___x_1901_ = lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_head_1898_) == 2 {
                    v_constName_1909_ = lean_ctor_get(v_head_1898_, 0);
                    lean_inc(v_constName_1909_);
                    lean_dec_ref_known(v_head_1898_, 1);
                    v___y_1904_ = v_constName_1909_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_head_1898_);
                    v___x_1910_ = lean_box(0);
                    v___y_1904_ = v___x_1910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1902_ == 0 {
                    lean_ctor_set(v___x_1901_, 1, v_a_1896_);
                    lean_ctor_set(v___x_1901_, 0, v___y_1904_);
                    v___x_1906_ = v___x_1901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___y_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1896_);
                    v___x_1906_ = v_reuseFailAlloc_1908_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1895_ = v_tail_1899_;
                v_a_1896_ = v___x_1906_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(
    mut v_s_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1913_ = lean_box(0);
    v___x_1914_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(v_s_1912_, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(
    mut v_a_1915_: *mut LeanObject,
    mut v_a_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1915_) == 0 {
                    v___x_1917_ = l_List_reverse___redArg(v_a_1916_);
                    return v___x_1917_;
                } else {
                    v_head_1918_ = lean_ctor_get(v_a_1915_, 0);
                    v_tail_1919_ = lean_ctor_get(v_a_1915_, 1);
                    v_isSharedCheck_1928_ = (!lean_is_exclusive(v_a_1915_)) as u8;
                    if v_isSharedCheck_1928_ == 0 {
                        v___x_1921_ = v_a_1915_;
                        v_isShared_1922_ = v_isSharedCheck_1928_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1919_);
                        lean_inc(v_head_1918_);
                        lean_dec(v_a_1915_);
                        v___x_1921_ = lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1928_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1923_ = l_Lean_MessageData_ofName(v_head_1918_);
                if v_isShared_1922_ == 0 {
                    lean_ctor_set(v___x_1921_, 1, v_a_1916_);
                    lean_ctor_set(v___x_1921_, 0, v___x_1923_);
                    v___x_1925_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1923_);
                    lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1916_);
                    v___x_1925_ = v_reuseFailAlloc_1927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1915_ = v_tail_1919_;
                v_a_1916_ = v___x_1925_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1929_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_1931_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1931_, 0, v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1932_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1933_ = lean_unsigned_to_nat(0);
    v___x_1934_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1934_, 0, v___x_1933_);
    lean_ctor_set(v___x_1934_, 1, v___x_1933_);
    lean_ctor_set(v___x_1934_, 2, v___x_1933_);
    lean_ctor_set(v___x_1934_, 3, v___x_1933_);
    lean_ctor_set(v___x_1934_, 4, v___x_1932_);
    lean_ctor_set(v___x_1934_, 5, v___x_1932_);
    lean_ctor_set(v___x_1934_, 6, v___x_1932_);
    lean_ctor_set(v___x_1934_, 7, v___x_1932_);
    lean_ctor_set(v___x_1934_, 8, v___x_1932_);
    lean_ctor_set(v___x_1934_, 9, v___x_1932_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    v___x_1935_ = lean_unsigned_to_nat(32);
    v___x_1936_ = lean_mk_empty_array_with_capacity(v___x_1935_);
    v___x_1937_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    v___x_1938_ = 5usize;
    v___x_1939_ = lean_unsigned_to_nat(0);
    v___x_1940_ = lean_unsigned_to_nat(32);
    v___x_1941_ = lean_mk_empty_array_with_capacity(v___x_1940_);
    v___x_1942_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_1943_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1943_, 0, v___x_1942_);
    lean_ctor_set(v___x_1943_, 1, v___x_1941_);
    lean_ctor_set(v___x_1943_, 2, v___x_1939_);
    lean_ctor_set(v___x_1943_, 3, v___x_1939_);
    lean_ctor_set_usize(v___x_1943_, 4, v___x_1938_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    v___x_1944_ = lean_box(1);
    v___x_1945_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_1946_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1947_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1947_, 0, v___x_1946_);
    lean_ctor_set(v___x_1947_, 1, v___x_1945_);
    lean_ctor_set(v___x_1947_, 2, v___x_1944_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1950_ = l_Lean_stringToMessageData(v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_1962_ = l_Lean_stringToMessageData(v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1967_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1969_: *mut LeanObject,
    mut v_declHint_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v_isExporting_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1973_ = lean_st_ref_get(v___y_1971_);
                v_env_1974_ = lean_ctor_get(v___x_1973_, 0);
                lean_inc_ref(v_env_1974_);
                lean_dec(v___x_1973_);
                v___x_1975_ = l_Lean_Name_isAnonymous(v_declHint_1970_);
                if v___x_1975_ == 0 {
                    v_isExporting_1976_ = lean_ctor_get_uint8(
                        v_env_1974_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1976_ == 0 {
                        lean_dec_ref(v_env_1974_);
                        lean_dec(v_declHint_1970_);
                        v___x_1977_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1977_, 0, v_msg_1969_);
                        return v___x_1977_;
                    } else {
                        lean_inc_ref(v_env_1974_);
                        v___x_1978_ = l_Lean_Environment_setExporting(v_env_1974_, v___x_1975_);
                        lean_inc(v_declHint_1970_);
                        lean_inc_ref(v___x_1978_);
                        v___x_1979_ = l_Lean_Environment_contains(
                            v___x_1978_,
                            v_declHint_1970_,
                            v_isExporting_1976_,
                        );
                        if v___x_1979_ == 0 {
                            lean_dec_ref(v___x_1978_);
                            lean_dec_ref(v_env_1974_);
                            lean_dec(v_declHint_1970_);
                            v___x_1980_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1980_, 0, v_msg_1969_);
                            return v___x_1980_;
                        } else {
                            v___x_1981_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_1982_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_1983_ = l_Lean_Options_empty;
                            v___x_1984_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1984_, 0, v___x_1978_);
                            lean_ctor_set(v___x_1984_, 1, v___x_1981_);
                            lean_ctor_set(v___x_1984_, 2, v___x_1982_);
                            lean_ctor_set(v___x_1984_, 3, v___x_1983_);
                            lean_inc(v_declHint_1970_);
                            v___x_1985_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1970_, v___x_1975_);
                            v_c_1986_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1986_, 0, v___x_1984_);
                            lean_ctor_set(v_c_1986_, 1, v___x_1985_);
                            v___x_1987_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1974_,
                                v_declHint_1970_,
                            );
                            if lean_obj_tag(v___x_1987_) == 0 {
                                lean_dec_ref(v_env_1974_);
                                lean_dec(v_declHint_1970_);
                                v___x_1988_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_1989_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1989_, 0, v___x_1988_);
                                lean_ctor_set(v___x_1989_, 1, v_c_1986_);
                                v___x_1990_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_1991_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1991_, 0, v___x_1989_);
                                lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                                v___x_1992_ = l_Lean_MessageData_note(v___x_1991_);
                                v___x_1993_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1993_, 0, v_msg_1969_);
                                lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                                v___x_1994_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1994_, 0, v___x_1993_);
                                return v___x_1994_;
                            } else {
                                v_val_1995_ = lean_ctor_get(v___x_1987_, 0);
                                v_isSharedCheck_2030_ = (!lean_is_exclusive(v___x_1987_)) as u8;
                                if v_isSharedCheck_2030_ == 0 {
                                    v___x_1997_ = v___x_1987_;
                                    v_isShared_1998_ = v_isSharedCheck_2030_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1995_);
                                    lean_dec(v___x_1987_);
                                    v___x_1997_ = lean_box(0);
                                    v_isShared_1998_ = v_isSharedCheck_2030_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1974_);
                    lean_dec(v_declHint_1970_);
                    v___x_2031_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2031_, 0, v_msg_1969_);
                    return v___x_2031_;
                }
            }
            1 => {
                v___x_1999_ = lean_box(0);
                v___x_2000_ = l_Lean_Environment_header(v_env_1974_);
                lean_dec_ref(v_env_1974_);
                v___x_2001_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2000_);
                v_mod_2002_ = lean_array_get(v___x_1999_, v___x_2001_, v_val_1995_);
                lean_dec(v_val_1995_);
                lean_dec_ref(v___x_2001_);
                v___x_2003_ = l_Lean_isPrivateName(v_declHint_1970_);
                lean_dec(v_declHint_1970_);
                if v___x_2003_ == 0 {
                    v___x_2004_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_2005_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2005_, 0, v___x_2004_);
                    lean_ctor_set(v___x_2005_, 1, v_c_1986_);
                    v___x_2006_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_2007_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2007_, 0, v___x_2005_);
                    lean_ctor_set(v___x_2007_, 1, v___x_2006_);
                    v___x_2008_ = l_Lean_MessageData_ofName(v_mod_2002_);
                    v___x_2009_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2009_, 0, v___x_2007_);
                    lean_ctor_set(v___x_2009_, 1, v___x_2008_);
                    v___x_2010_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_2011_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2011_, 0, v___x_2009_);
                    lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                    v___x_2012_ = l_Lean_MessageData_note(v___x_2011_);
                    v___x_2013_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2013_, 0, v_msg_1969_);
                    lean_ctor_set(v___x_2013_, 1, v___x_2012_);
                    if v_isShared_1998_ == 0 {
                        lean_ctor_set_tag(v___x_1997_, 0);
                        lean_ctor_set(v___x_1997_, 0, v___x_2013_);
                        v___x_2015_ = v___x_1997_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
                        v___x_2015_ = v_reuseFailAlloc_2016_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2017_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_2018_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                    lean_ctor_set(v___x_2018_, 1, v_c_1986_);
                    v___x_2019_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_2020_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2020_, 0, v___x_2018_);
                    lean_ctor_set(v___x_2020_, 1, v___x_2019_);
                    v___x_2021_ = l_Lean_MessageData_ofName(v_mod_2002_);
                    v___x_2022_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2022_, 0, v___x_2020_);
                    lean_ctor_set(v___x_2022_, 1, v___x_2021_);
                    v___x_2023_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_2024_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2024_, 0, v___x_2022_);
                    lean_ctor_set(v___x_2024_, 1, v___x_2023_);
                    v___x_2025_ = l_Lean_MessageData_note(v___x_2024_);
                    v___x_2026_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2026_, 0, v_msg_1969_);
                    lean_ctor_set(v___x_2026_, 1, v___x_2025_);
                    if v_isShared_1998_ == 0 {
                        lean_ctor_set_tag(v___x_1997_, 0);
                        lean_ctor_set(v___x_1997_, 0, v___x_2026_);
                        v___x_2028_ = v___x_1997_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                        v___x_2028_ = v_reuseFailAlloc_2029_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2015_;
            }
            3 => {
                return v___x_2028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_2032_: *mut LeanObject,
    mut v_declHint_2033_: *mut LeanObject,
    mut v___y_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2036_: *mut LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2032_, v_declHint_2033_, v___y_2034_);
    lean_dec(v___y_2034_);
    return v_res_2036_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_2037_: *mut LeanObject,
    mut v_declHint_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
    mut v___y_2040_: *mut LeanObject,
    mut v___y_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2044_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2037_, v_declHint_2038_, v___y_2042_);
                v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
                v_isSharedCheck_2054_ = (!lean_is_exclusive(v___x_2044_)) as u8;
                if v_isSharedCheck_2054_ == 0 {
                    v___x_2047_ = v___x_2044_;
                    v_isShared_2048_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2045_);
                    lean_dec(v___x_2044_);
                    v___x_2047_ = lean_box(0);
                    v_isShared_2048_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2049_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2050_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2050_, 0, v___x_2049_);
                lean_ctor_set(v___x_2050_, 1, v_a_2045_);
                if v_isShared_2048_ == 0 {
                    lean_ctor_set(v___x_2047_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_2055_: *mut LeanObject,
    mut v_declHint_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2062_: *mut LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2055_, v_declHint_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
    lean_dec(v___y_2060_);
    lean_dec_ref(v___y_2059_);
    lean_dec(v___y_2058_);
    lean_dec_ref(v___y_2057_);
    return v_res_2062_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_2063_: *mut LeanObject,
    mut v_msg_2064_: *mut LeanObject,
    mut v___y_2065_: *mut LeanObject,
    mut v___y_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2082_: u8 = 0;
    let mut v_cancelTk_x3f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2084_: u8 = 0;
    let mut v_inheritedTraceOptions_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2070_ = lean_ctor_get(v___y_2067_, 0);
    v_fileMap_2071_ = lean_ctor_get(v___y_2067_, 1);
    v_options_2072_ = lean_ctor_get(v___y_2067_, 2);
    v_currRecDepth_2073_ = lean_ctor_get(v___y_2067_, 3);
    v_maxRecDepth_2074_ = lean_ctor_get(v___y_2067_, 4);
    v_ref_2075_ = lean_ctor_get(v___y_2067_, 5);
    v_currNamespace_2076_ = lean_ctor_get(v___y_2067_, 6);
    v_openDecls_2077_ = lean_ctor_get(v___y_2067_, 7);
    v_initHeartbeats_2078_ = lean_ctor_get(v___y_2067_, 8);
    v_maxHeartbeats_2079_ = lean_ctor_get(v___y_2067_, 9);
    v_quotContext_2080_ = lean_ctor_get(v___y_2067_, 10);
    v_currMacroScope_2081_ = lean_ctor_get(v___y_2067_, 11);
    v_diag_2082_ = lean_ctor_get_uint8(
        v___y_2067_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2083_ = lean_ctor_get(v___y_2067_, 12);
    v_suppressElabErrors_2084_ = lean_ctor_get_uint8(
        v___y_2067_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2085_ = lean_ctor_get(v___y_2067_, 13);
    v_ref_2086_ = l_Lean_replaceRef(v_ref_2063_, v_ref_2075_);
    lean_inc_ref(v_inheritedTraceOptions_2085_);
    lean_inc(v_cancelTk_x3f_2083_);
    lean_inc(v_currMacroScope_2081_);
    lean_inc(v_quotContext_2080_);
    lean_inc(v_maxHeartbeats_2079_);
    lean_inc(v_initHeartbeats_2078_);
    lean_inc(v_openDecls_2077_);
    lean_inc(v_currNamespace_2076_);
    lean_inc(v_maxRecDepth_2074_);
    lean_inc(v_currRecDepth_2073_);
    lean_inc_ref(v_options_2072_);
    lean_inc_ref(v_fileMap_2071_);
    lean_inc_ref(v_fileName_2070_);
    v___x_2087_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2087_, 0, v_fileName_2070_);
    lean_ctor_set(v___x_2087_, 1, v_fileMap_2071_);
    lean_ctor_set(v___x_2087_, 2, v_options_2072_);
    lean_ctor_set(v___x_2087_, 3, v_currRecDepth_2073_);
    lean_ctor_set(v___x_2087_, 4, v_maxRecDepth_2074_);
    lean_ctor_set(v___x_2087_, 5, v_ref_2086_);
    lean_ctor_set(v___x_2087_, 6, v_currNamespace_2076_);
    lean_ctor_set(v___x_2087_, 7, v_openDecls_2077_);
    lean_ctor_set(v___x_2087_, 8, v_initHeartbeats_2078_);
    lean_ctor_set(v___x_2087_, 9, v_maxHeartbeats_2079_);
    lean_ctor_set(v___x_2087_, 10, v_quotContext_2080_);
    lean_ctor_set(v___x_2087_, 11, v_currMacroScope_2081_);
    lean_ctor_set(v___x_2087_, 12, v_cancelTk_x3f_2083_);
    lean_ctor_set(v___x_2087_, 13, v_inheritedTraceOptions_2085_);
    lean_ctor_set_uint8(
        v___x_2087_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2082_,
    );
    lean_ctor_set_uint8(
        v___x_2087_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2084_,
    );
    v___x_2088_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_2064_, v___y_2065_, v___y_2066_, v___x_2087_, v___y_2068_);
    lean_dec_ref_known(v___x_2087_, 14);
    return v___x_2088_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_2089_: *mut LeanObject,
    mut v_msg_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2089_, v_msg_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    lean_dec(v___y_2092_);
    lean_dec_ref(v___y_2091_);
    lean_dec(v_ref_2089_);
    return v_res_2096_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_2097_: *mut LeanObject,
    mut v_msg_2098_: *mut LeanObject,
    mut v_declHint_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2098_, v_declHint_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
    v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
    lean_inc(v_a_2106_);
    lean_dec_ref(v___x_2105_);
    v___x_2107_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2097_, v_a_2106_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
    return v___x_2107_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_2108_: *mut LeanObject,
    mut v_msg_2109_: *mut LeanObject,
    mut v_declHint_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
    mut v___y_2114_: *mut LeanObject,
    mut v___y_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2116_: *mut LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2108_, v_msg_2109_, v_declHint_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
    lean_dec(v___y_2114_);
    lean_dec_ref(v___y_2113_);
    lean_dec(v___y_2112_);
    lean_dec_ref(v___y_2111_);
    lean_dec(v_ref_2108_);
    return v_res_2116_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2123_: *mut LeanObject,
    mut v_constName_2124_: *mut LeanObject,
    mut v___y_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    v___x_2130_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2131_ = 0;
    lean_inc(v_constName_2124_);
    v___x_2132_ = l_Lean_MessageData_ofConstName(v_constName_2124_, v___x_2131_);
    v___x_2133_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2133_, 0, v___x_2130_);
    lean_ctor_set(v___x_2133_, 1, v___x_2132_);
    v___x_2134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2135_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2135_, 0, v___x_2133_);
    lean_ctor_set(v___x_2135_, 1, v___x_2134_);
    v___x_2136_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2123_, v___x_2135_, v_constName_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2137_: *mut LeanObject,
    mut v_constName_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v___y_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2144_: *mut LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2137_, v_constName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
    lean_dec(v___y_2142_);
    lean_dec_ref(v___y_2141_);
    lean_dec(v___y_2140_);
    lean_dec_ref(v___y_2139_);
    lean_dec(v_ref_2137_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(
    mut v_constName_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2151_ = lean_ctor_get(v___y_2148_, 5);
    v___x_2152_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2151_, v_constName_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
    return v___x_2152_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg___boxed(
    mut v_constName_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
    mut v___y_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    lean_dec(v___y_2157_);
    lean_dec_ref(v___y_2156_);
    lean_dec(v___y_2155_);
    lean_dec_ref(v___y_2154_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
    mut v_constName_2160_: *mut LeanObject,
    mut v___y_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = lean_st_ref_get(v___y_2164_);
                v_env_2167_ = lean_ctor_get(v___x_2166_, 0);
                lean_inc_ref(v_env_2167_);
                lean_dec(v___x_2166_);
                v___x_2168_ = 0;
                lean_inc(v_constName_2160_);
                v___x_2169_ =
                    l_Lean_Environment_find_x3f(v_env_2167_, v_constName_2160_, v___x_2168_);
                if lean_obj_tag(v___x_2169_) == 0 {
                    v___x_2170_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
                    return v___x_2170_;
                } else {
                    lean_dec(v_constName_2160_);
                    v_val_2171_ = lean_ctor_get(v___x_2169_, 0);
                    v_isSharedCheck_2178_ = (!lean_is_exclusive(v___x_2169_)) as u8;
                    if v_isSharedCheck_2178_ == 0 {
                        v___x_2173_ = v___x_2169_;
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2171_);
                        lean_dec(v___x_2169_);
                        v___x_2173_ = lean_box(0);
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2174_ == 0 {
                    lean_ctor_set_tag(v___x_2173_, 0);
                    v___x_2176_ = v___x_2173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2171_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0___boxed(
    mut v_constName_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
        v_constName_2179_,
        v___y_2180_,
        v___y_2181_,
        v___y_2182_,
        v___y_2183_,
    );
    lean_dec(v___y_2183_);
    lean_dec_ref(v___y_2182_);
    lean_dec(v___y_2181_);
    lean_dec_ref(v___y_2180_);
    return v_res_2185_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0()
-> f64 {
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: f64 = 0.0;
    v___x_2186_ = lean_unsigned_to_nat(0);
    v___x_2187_ = lean_float_of_nat(v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
    mut v_cls_2191_: *mut LeanObject,
    mut v_msg_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v_tid_2217_: u64 = 0;
    let mut v_traces_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: f64 = 0.0;
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2198_ = lean_ctor_get(v___y_2195_, 5);
                v___x_2199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
                v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
                v_isSharedCheck_2244_ = (!lean_is_exclusive(v___x_2199_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2202_ = v___x_2199_;
                    v_isShared_2203_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2200_);
                    lean_dec(v___x_2199_);
                    v___x_2202_ = lean_box(0);
                    v_isShared_2203_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2204_ = lean_st_ref_take(v___y_2196_);
                v_traceState_2205_ = lean_ctor_get(v___x_2204_, 4);
                v_env_2206_ = lean_ctor_get(v___x_2204_, 0);
                v_nextMacroScope_2207_ = lean_ctor_get(v___x_2204_, 1);
                v_ngen_2208_ = lean_ctor_get(v___x_2204_, 2);
                v_auxDeclNGen_2209_ = lean_ctor_get(v___x_2204_, 3);
                v_cache_2210_ = lean_ctor_get(v___x_2204_, 5);
                v_messages_2211_ = lean_ctor_get(v___x_2204_, 6);
                v_infoState_2212_ = lean_ctor_get(v___x_2204_, 7);
                v_snapshotTasks_2213_ = lean_ctor_get(v___x_2204_, 8);
                v_isSharedCheck_2243_ = (!lean_is_exclusive(v___x_2204_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2215_ = v___x_2204_;
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2213_);
                    lean_inc(v_infoState_2212_);
                    lean_inc(v_messages_2211_);
                    lean_inc(v_cache_2210_);
                    lean_inc(v_traceState_2205_);
                    lean_inc(v_auxDeclNGen_2209_);
                    lean_inc(v_ngen_2208_);
                    lean_inc(v_nextMacroScope_2207_);
                    lean_inc(v_env_2206_);
                    lean_dec(v___x_2204_);
                    v___x_2215_ = lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2217_ = lean_ctor_get_uint64(
                    v_traceState_2205_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2218_ = lean_ctor_get(v_traceState_2205_, 0);
                v_isSharedCheck_2242_ = (!lean_is_exclusive(v_traceState_2205_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v___x_2220_ = v_traceState_2205_;
                    v_isShared_2221_ = v_isSharedCheck_2242_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2218_);
                    lean_dec(v_traceState_2205_);
                    v___x_2220_ = lean_box(0);
                    v_isShared_2221_ = v_isSharedCheck_2242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2222_ = lean_box(0);
                v___x_2223_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0);
                v___x_2224_ = 0;
                v___x_2225_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1;
                v___x_2226_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2226_, 0, v_cls_2191_);
                lean_ctor_set(v___x_2226_, 1, v___x_2222_);
                lean_ctor_set(v___x_2226_, 2, v___x_2225_);
                lean_ctor_set_float(
                    v___x_2226_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2223_,
                );
                lean_ctor_set_float(
                    v___x_2226_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2223_,
                );
                lean_ctor_set_uint8(
                    v___x_2226_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2224_,
                );
                v___x_2227_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2;
                v___x_2228_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2228_, 0, v___x_2226_);
                lean_ctor_set(v___x_2228_, 1, v_a_2200_);
                lean_ctor_set(v___x_2228_, 2, v___x_2227_);
                lean_inc(v_ref_2198_);
                v___x_2229_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2229_, 0, v_ref_2198_);
                lean_ctor_set(v___x_2229_, 1, v___x_2228_);
                v___x_2230_ = l_Lean_PersistentArray_push___redArg(v_traces_2218_, v___x_2229_);
                if v_isShared_2221_ == 0 {
                    lean_ctor_set(v___x_2220_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2230_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2217_,
                    );
                    v___x_2232_ = v_reuseFailAlloc_2241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2216_ == 0 {
                    lean_ctor_set(v___x_2215_, 4, v___x_2232_);
                    v___x_2234_ = v___x_2215_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_env_2206_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_nextMacroScope_2207_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_ngen_2208_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_auxDeclNGen_2209_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 4, v___x_2232_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 5, v_cache_2210_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 6, v_messages_2211_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 7, v_infoState_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 8, v_snapshotTasks_2213_);
                    v___x_2234_ = v_reuseFailAlloc_2240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2235_ = lean_st_ref_set(v___y_2196_, v___x_2234_);
                v___x_2236_ = lean_box(0);
                if v_isShared_2203_ == 0 {
                    lean_ctor_set(v___x_2202_, 0, v___x_2236_);
                    v___x_2238_ = v___x_2202_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2239_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___boxed(
    mut v_cls_2245_: *mut LeanObject,
    mut v_msg_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
        v_cls_2245_,
        v_msg_2246_,
        v___y_2247_,
        v___y_2248_,
        v___y_2249_,
        v___y_2250_,
    );
    lean_dec(v___y_2250_);
    lean_dec_ref(v___y_2249_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    return v_res_2252_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3() -> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_2259_ = l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2;
    v___x_2260_ = l_Lean_Name_append(v___x_2259_, v___x_2258_);
    return v___x_2260_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5() -> *mut LeanObject {
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4;
    v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lean_Meta_Grind_mkInjectiveTheorem(
    mut v_declName_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2276_: u8 = 0;
    let mut v___y_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: u8 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2289_: u8 = 0;
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_a_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: u8 = 0;
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v_a_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_a_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_2264_);
                v___x_2270_ =
                    l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
                        v_declName_2264_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                if lean_obj_tag(v___x_2270_) == 0 {
                    v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
                    lean_inc(v_a_2271_);
                    lean_dec_ref_known(v___x_2270_, 1);
                    lean_inc(v_declName_2264_);
                    v___x_2272_ = l_Lean_Meta_Grind_getProofForDecl(
                        v_declName_2264_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                    if lean_obj_tag(v___x_2272_) == 0 {
                        v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
                        v_isSharedCheck_2325_ = (!lean_is_exclusive(v___x_2272_)) as u8;
                        if v_isSharedCheck_2325_ == 0 {
                            v___x_2275_ = v___x_2272_;
                            v_isShared_2276_ = v_isSharedCheck_2325_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2273_);
                            lean_dec(v___x_2272_);
                            v___x_2275_ = lean_box(0);
                            v_isShared_2276_ = v_isSharedCheck_2325_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2271_);
                        lean_dec(v_declName_2264_);
                        v_a_2326_ = lean_ctor_get(v___x_2272_, 0);
                        v_isSharedCheck_2333_ = (!lean_is_exclusive(v___x_2272_)) as u8;
                        if v_isSharedCheck_2333_ == 0 {
                            v___x_2328_ = v___x_2272_;
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2326_);
                            lean_dec(v___x_2272_);
                            v___x_2328_ = lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_2264_);
                    v_a_2334_ = lean_ctor_get(v___x_2270_, 0);
                    v_isSharedCheck_2341_ = (!lean_is_exclusive(v___x_2270_)) as u8;
                    if v_isSharedCheck_2341_ == 0 {
                        v___x_2336_ = v___x_2270_;
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2334_);
                        lean_dec(v___x_2270_);
                        v___x_2336_ = lean_box(0);
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2321_ = l_Lean_ConstantInfo_levelParams(v_a_2271_);
                lean_dec(v_a_2271_);
                v___x_2322_ = l_List_isEmpty___redArg(v___x_2321_);
                lean_dec(v___x_2321_);
                if v___x_2322_ == 0 {
                    v___x_2323_ = 1;
                    v___y_2286_ = v___x_2323_;
                    state = 4;
                    continue;
                } else {
                    v___x_2324_ = 0;
                    v___y_2286_ = v___x_2324_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2279_ = l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0;
                v___x_2280_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2280_, 0, v_declName_2264_);
                v___x_2281_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2281_, 0, v___x_2279_);
                lean_ctor_set(v___x_2281_, 1, v_a_2273_);
                lean_ctor_set(v___x_2281_, 2, v___y_2278_);
                lean_ctor_set(v___x_2281_, 3, v___x_2280_);
                if v_isShared_2276_ == 0 {
                    lean_ctor_set(v___x_2275_, 0, v___x_2281_);
                    v___x_2283_ = v___x_2275_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2283_;
            }
            4 => {
                lean_inc(v_a_2273_);
                v___x_2287_ =
                    l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
                        v_a_2273_,
                        v___y_2286_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                if lean_obj_tag(v___x_2287_) == 0 {
                    v_options_2288_ = lean_ctor_get(v_a_2267_, 2);
                    v_hasTrace_2289_ = lean_ctor_get_uint8(
                        v_options_2288_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2289_ == 0 {
                        v_a_2290_ = lean_ctor_get(v___x_2287_, 0);
                        lean_inc(v_a_2290_);
                        lean_dec_ref_known(v___x_2287_, 1);
                        v___y_2278_ = v_a_2290_;
                        state = 2;
                        continue;
                    } else {
                        v_a_2291_ = lean_ctor_get(v___x_2287_, 0);
                        lean_inc(v_a_2291_);
                        lean_dec_ref_known(v___x_2287_, 1);
                        v_inheritedTraceOptions_2292_ = lean_ctor_get(v_a_2267_, 13);
                        v___x_2293_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
                        v___x_2294_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3,
                        );
                        v___x_2295_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2292_,
                            v_options_2288_,
                            v___x_2294_,
                        );
                        if v___x_2295_ == 0 {
                            v___y_2278_ = v_a_2291_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_declName_2264_);
                            v___x_2296_ = l_Lean_MessageData_ofName(v_declName_2264_);
                            v___x_2297_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once
                                ),
                                _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5,
                            );
                            v___x_2298_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                            lean_ctor_set(v___x_2298_, 1, v___x_2297_);
                            lean_inc(v_a_2291_);
                            v___x_2299_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(v_a_2291_);
                            v___x_2300_ = lean_box(0);
                            v___x_2301_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(v___x_2299_, v___x_2300_);
                            v___x_2302_ = l_Lean_MessageData_ofList(v___x_2301_);
                            v___x_2303_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2303_, 0, v___x_2298_);
                            lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                            v___x_2304_ =
                                l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
                                    v___x_2293_,
                                    v___x_2303_,
                                    v_a_2265_,
                                    v_a_2266_,
                                    v_a_2267_,
                                    v_a_2268_,
                                );
                            if lean_obj_tag(v___x_2304_) == 0 {
                                lean_dec_ref_known(v___x_2304_, 1);
                                v___y_2278_ = v_a_2291_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2291_);
                                lean_del_object(v___x_2275_);
                                lean_dec(v_a_2273_);
                                lean_dec(v_declName_2264_);
                                v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
                                v_isSharedCheck_2312_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                                if v_isSharedCheck_2312_ == 0 {
                                    v___x_2307_ = v___x_2304_;
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_2305_);
                                    lean_dec(v___x_2304_);
                                    v___x_2307_ = lean_box(0);
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2275_);
                    lean_dec(v_a_2273_);
                    lean_dec(v_declName_2264_);
                    v_a_2313_ = lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2320_ = (!lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2315_ = v___x_2287_;
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2313_);
                        lean_dec(v___x_2287_);
                        v___x_2315_ = lean_box(0);
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_2308_ == 0 {
                    v___x_2310_ = v___x_2307_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
                    v___x_2310_ = v_reuseFailAlloc_2311_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2310_;
            }
            7 => {
                if v_isShared_2316_ == 0 {
                    v___x_2318_ = v___x_2315_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2318_;
            }
            9 => {
                if v_isShared_2329_ == 0 {
                    v___x_2331_ = v___x_2328_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2331_;
            }
            11 => {
                if v_isShared_2337_ == 0 {
                    v___x_2339_ = v___x_2336_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkInjectiveTheorem___boxed(
    mut v_declName_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2348_: *mut LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_Lean_Meta_Grind_mkInjectiveTheorem(
        v_declName_2342_,
        v_a_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
    );
    lean_dec(v_a_2346_);
    lean_dec_ref(v_a_2345_);
    lean_dec(v_a_2344_);
    lean_dec_ref(v_a_2343_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(
    mut v_00_u03b1_2349_: *mut LeanObject,
    mut v_constName_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    v___x_2356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___boxed(
    mut v_00_u03b1_2357_: *mut LeanObject,
    mut v_constName_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2364_: *mut LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(v_00_u03b1_2357_, v_constName_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
    lean_dec(v___y_2362_);
    lean_dec_ref(v___y_2361_);
    lean_dec(v___y_2360_);
    lean_dec_ref(v___y_2359_);
    return v_res_2364_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2365_: *mut LeanObject,
    mut v_ref_2366_: *mut LeanObject,
    mut v_constName_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    v___x_2373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2366_, v_constName_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
    return v___x_2373_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2374_: *mut LeanObject,
    mut v_ref_2375_: *mut LeanObject,
    mut v_constName_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(v_00_u03b1_2374_, v_ref_2375_, v_constName_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
    lean_dec(v___y_2380_);
    lean_dec_ref(v___y_2379_);
    lean_dec(v___y_2378_);
    lean_dec_ref(v___y_2377_);
    lean_dec(v_ref_2375_);
    return v_res_2382_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_2383_: *mut LeanObject,
    mut v_ref_2384_: *mut LeanObject,
    mut v_msg_2385_: *mut LeanObject,
    mut v_declHint_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2384_, v_msg_2385_, v_declHint_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_2393_: *mut LeanObject,
    mut v_ref_2394_: *mut LeanObject,
    mut v_msg_2395_: *mut LeanObject,
    mut v_declHint_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2402_: *mut LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2393_, v_ref_2394_, v_msg_2395_, v_declHint_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
    lean_dec(v___y_2400_);
    lean_dec_ref(v___y_2399_);
    lean_dec(v___y_2398_);
    lean_dec_ref(v___y_2397_);
    lean_dec(v_ref_2394_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_2403_: *mut LeanObject,
    mut v_declHint_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    v___x_2410_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2403_, v_declHint_2404_, v___y_2408_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_2411_: *mut LeanObject,
    mut v_declHint_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
    mut v___y_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2411_, v_declHint_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    lean_dec(v___y_2416_);
    lean_dec_ref(v___y_2415_);
    lean_dec(v___y_2414_);
    lean_dec_ref(v___y_2413_);
    return v_res_2418_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_2419_: *mut LeanObject,
    mut v_ref_2420_: *mut LeanObject,
    mut v_msg_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2420_, v_msg_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
    return v___x_2427_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_2428_: *mut LeanObject,
    mut v_ref_2429_: *mut LeanObject,
    mut v_msg_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2428_, v_ref_2429_, v_msg_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
    lean_dec(v___y_2434_);
    lean_dec_ref(v___y_2433_);
    lean_dec(v___y_2432_);
    lean_dec_ref(v___y_2431_);
    lean_dec(v_ref_2429_);
    return v_res_2436_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2437_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    v___x_2438_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0);
    v___x_2439_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2439_, 0, v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    v___x_2440_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
    v___x_2441_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2441_, 0, v___x_2440_);
    lean_ctor_set(v___x_2441_, 1, v___x_2440_);
    return v___x_2441_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
    v___x_2443_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2443_, 0, v___x_2442_);
    lean_ctor_set(v___x_2443_, 1, v___x_2442_);
    lean_ctor_set(v___x_2443_, 2, v___x_2442_);
    lean_ctor_set(v___x_2443_, 3, v___x_2442_);
    lean_ctor_set(v___x_2443_, 4, v___x_2442_);
    lean_ctor_set(v___x_2443_, 5, v___x_2442_);
    return v___x_2443_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(
    mut v_ext_2444_: *mut LeanObject,
    mut v_b_2445_: *mut LeanObject,
    mut v_kind_2446_: u8,
    mut v___y_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_unused_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_unused_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_2451_ = lean_ctor_get(v___y_2448_, 6);
                v___x_2452_ = lean_st_ref_take(v___y_2449_);
                v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
                v_nextMacroScope_2454_ = lean_ctor_get(v___x_2452_, 1);
                v_ngen_2455_ = lean_ctor_get(v___x_2452_, 2);
                v_auxDeclNGen_2456_ = lean_ctor_get(v___x_2452_, 3);
                v_traceState_2457_ = lean_ctor_get(v___x_2452_, 4);
                v_messages_2458_ = lean_ctor_get(v___x_2452_, 6);
                v_infoState_2459_ = lean_ctor_get(v___x_2452_, 7);
                v_snapshotTasks_2460_ = lean_ctor_get(v___x_2452_, 8);
                v_isSharedCheck_2487_ = (!lean_is_exclusive(v___x_2452_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v_unused_2488_ = lean_ctor_get(v___x_2452_, 5);
                    lean_dec(v_unused_2488_);
                    v___x_2462_ = v___x_2452_;
                    v_isShared_2463_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2460_);
                    lean_inc(v_infoState_2459_);
                    lean_inc(v_messages_2458_);
                    lean_inc(v_traceState_2457_);
                    lean_inc(v_auxDeclNGen_2456_);
                    lean_inc(v_ngen_2455_);
                    lean_inc(v_nextMacroScope_2454_);
                    lean_inc(v_env_2453_);
                    lean_dec(v___x_2452_);
                    v___x_2462_ = lean_box(0);
                    v_isShared_2463_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_2451_);
                v___x_2464_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_2453_,
                    v_ext_2444_,
                    v_b_2445_,
                    v_kind_2446_,
                    v_currNamespace_2451_,
                );
                v___x_2465_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2);
                if v_isShared_2463_ == 0 {
                    lean_ctor_set(v___x_2462_, 5, v___x_2465_);
                    lean_ctor_set(v___x_2462_, 0, v___x_2464_);
                    v___x_2467_ = v___x_2462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2464_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_nextMacroScope_2454_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_ngen_2455_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_auxDeclNGen_2456_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_traceState_2457_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 5, v___x_2465_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 6, v_messages_2458_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 7, v_infoState_2459_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 8, v_snapshotTasks_2460_);
                    v___x_2467_ = v_reuseFailAlloc_2486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2468_ = lean_st_ref_set(v___y_2449_, v___x_2467_);
                v___x_2469_ = lean_st_ref_take(v___y_2447_);
                v_mctx_2470_ = lean_ctor_get(v___x_2469_, 0);
                v_zetaDeltaFVarIds_2471_ = lean_ctor_get(v___x_2469_, 2);
                v_postponed_2472_ = lean_ctor_get(v___x_2469_, 3);
                v_diag_2473_ = lean_ctor_get(v___x_2469_, 4);
                v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2469_)) as u8;
                if v_isSharedCheck_2484_ == 0 {
                    v_unused_2485_ = lean_ctor_get(v___x_2469_, 1);
                    lean_dec(v_unused_2485_);
                    v___x_2475_ = v___x_2469_;
                    v_isShared_2476_ = v_isSharedCheck_2484_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_2473_);
                    lean_inc(v_postponed_2472_);
                    lean_inc(v_zetaDeltaFVarIds_2471_);
                    lean_inc(v_mctx_2470_);
                    lean_dec(v___x_2469_);
                    v___x_2475_ = lean_box(0);
                    v_isShared_2476_ = v_isSharedCheck_2484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2477_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3);
                if v_isShared_2476_ == 0 {
                    lean_ctor_set(v___x_2475_, 1, v___x_2477_);
                    v___x_2479_ = v___x_2475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_mctx_2470_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2477_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_zetaDeltaFVarIds_2471_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_postponed_2472_);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_diag_2473_);
                    v___x_2479_ = v_reuseFailAlloc_2483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2480_ = lean_st_ref_set(v___y_2447_, v___x_2479_);
                v___x_2481_ = lean_box(0);
                v___x_2482_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2482_, 0, v___x_2481_);
                return v___x_2482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___boxed(
    mut v_ext_2489_: *mut LeanObject,
    mut v_b_2490_: *mut LeanObject,
    mut v_kind_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2496_: u8 = 0;
    let mut v_res_2497_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2496_ = (lean_unbox(v_kind_2491_) as u8);
    v_res_2497_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2489_, v_b_2490_, v_kind_boxed_2496_, v___y_2492_, v___y_2493_, v___y_2494_);
    lean_dec(v___y_2494_);
    lean_dec_ref(v___y_2493_);
    lean_dec(v___y_2492_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(
    mut v_00_u03b1_2498_: *mut LeanObject,
    mut v_00_u03b2_2499_: *mut LeanObject,
    mut v_00_u03c3_2500_: *mut LeanObject,
    mut v_ext_2501_: *mut LeanObject,
    mut v_b_2502_: *mut LeanObject,
    mut v_kind_2503_: u8,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    v___x_2509_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2501_, v_b_2502_, v_kind_2503_, v___y_2505_, v___y_2506_, v___y_2507_);
    return v___x_2509_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___boxed(
    mut v_00_u03b1_2510_: *mut LeanObject,
    mut v_00_u03b2_2511_: *mut LeanObject,
    mut v_00_u03c3_2512_: *mut LeanObject,
    mut v_ext_2513_: *mut LeanObject,
    mut v_b_2514_: *mut LeanObject,
    mut v_kind_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2521_: u8 = 0;
    let mut v_res_2522_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2521_ = (lean_unbox(v_kind_2515_) as u8);
    v_res_2522_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(
            v_00_u03b1_2510_,
            v_00_u03b2_2511_,
            v_00_u03c3_2512_,
            v_ext_2513_,
            v_b_2514_,
            v_kind_boxed_2521_,
            v___y_2516_,
            v___y_2517_,
            v___y_2518_,
            v___y_2519_,
        );
    lean_dec(v___y_2519_);
    lean_dec_ref(v___y_2518_);
    lean_dec(v___y_2517_);
    lean_dec_ref(v___y_2516_);
    return v_res_2522_;
}
pub unsafe fn l_Lean_Meta_Grind_Extension_addInjectiveAttr(
    mut v_ext_2523_: *mut LeanObject,
    mut v_declName_2524_: *mut LeanObject,
    mut v_attrKind_2525_: u8,
    mut v_a_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2531_ = l_Lean_Meta_Grind_mkInjectiveTheorem(
                    v_declName_2524_,
                    v_a_2526_,
                    v_a_2527_,
                    v_a_2528_,
                    v_a_2529_,
                );
                if lean_obj_tag(v___x_2531_) == 0 {
                    v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
                    lean_inc(v_a_2532_);
                    lean_dec_ref_known(v___x_2531_, 1);
                    v___x_2533_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v___x_2533_, 0, v_a_2532_);
                    v___x_2534_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2523_, v___x_2533_, v_attrKind_2525_, v_a_2527_, v_a_2528_, v_a_2529_);
                    return v___x_2534_;
                } else {
                    lean_dec_ref(v_ext_2523_);
                    v_a_2535_ = lean_ctor_get(v___x_2531_, 0);
                    v_isSharedCheck_2542_ = (!lean_is_exclusive(v___x_2531_)) as u8;
                    if v_isSharedCheck_2542_ == 0 {
                        v___x_2537_ = v___x_2531_;
                        v_isShared_2538_ = v_isSharedCheck_2542_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2535_);
                        lean_dec(v___x_2531_);
                        v___x_2537_ = lean_box(0);
                        v_isShared_2538_ = v_isSharedCheck_2542_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2538_ == 0 {
                    v___x_2540_ = v___x_2537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
                    v___x_2540_ = v_reuseFailAlloc_2541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Extension_addInjectiveAttr___boxed(
    mut v_ext_2543_: *mut LeanObject,
    mut v_declName_2544_: *mut LeanObject,
    mut v_attrKind_2545_: *mut LeanObject,
    mut v_a_2546_: *mut LeanObject,
    mut v_a_2547_: *mut LeanObject,
    mut v_a_2548_: *mut LeanObject,
    mut v_a_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_2551_: u8 = 0;
    let mut v_res_2552_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_2551_ = (lean_unbox(v_attrKind_2545_) as u8);
    v_res_2552_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(
        v_ext_2543_,
        v_declName_2544_,
        v_attrKind_boxed_2551_,
        v_a_2546_,
        v_a_2547_,
        v_a_2548_,
        v_a_2549_,
    );
    lean_dec(v_a_2549_);
    lean_dec_ref(v_a_2548_);
    lean_dec(v_a_2547_);
    lean_dec_ref(v_a_2546_);
    return v_res_2552_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
}
