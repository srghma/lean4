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
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1891887995088964530 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,622053547050603573 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7466587695041019504 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,12476371541004604745 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17132214338911791756 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1550241582563015600 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12168955777775944890 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4539651995539963167 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6727391452282951466 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15194044346522623659 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7456218402816208931 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15292532237123326354 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6345104771979739696 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14920283104170040409 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 101, 114, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1891887995088964530 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16986677381411493332 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1215188614 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3751231088157539844 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8081854262743651883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15920477089225671659 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8453999917361367102 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14562555973890958749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value: crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 105, 110, 106, 101, 99, 116, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 109, 117, 115, 116, 32, 117, 115, 101, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 115, 121, 109, 98, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value: crate::leanh::LeanStringObject<78> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 78, m_capacity: 78, m_length: 77, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 116, 104, 101, 111, 114, 101, 109, 32, 104, 97, 115, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115, 44, 32, 98, 117, 116, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,920240211420121313 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14487767036850709044 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 105, 110, 106, 93, 96, 32, 116, 104, 101, 111, 114, 101, 109, 44, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 114, 109, 32, 96, 70, 117, 110, 99, 116, 105, 111, 110, 46, 73, 110, 106, 101, 99, 116, 105, 118, 101, 32, 60, 102, 117, 110, 62, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__1_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = crate::leanh::lean_unsigned_to_nat(3173337487);
    v___x_1342_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1343_ = l_Lean_Name_num___override(v___x_1342_, v___x_1341_);
    return v___x_1343_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1345_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1347_ = l_Lean_Name_str___override(v___x_1346_, v___x_1345_);
    return v___x_1347_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1350_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1351_ = l_Lean_Name_str___override(v___x_1350_, v___x_1349_);
    return v___x_1351_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1354_ = l_Lean_Name_num___override(v___x_1353_, v___x_1352_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1357_ = 0;
    v___x_1358_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_);
    v___x_1359_ = l_Lean_registerTraceClass(v___x_1356_, v___x_1357_, v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2____boxed(
    mut v_a_1360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
    return v_res_1361_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_;
    v___x_1381_ = 0;
    v___x_1382_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_;
    v___x_1383_ = l_Lean_registerTraceClass(v___x_1380_, v___x_1381_, v___x_1382_);
    return v___x_1383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2____boxed(
    mut v_a_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1385_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
    return v_res_1385_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = crate::leanh::lean_unsigned_to_nat(3941467707);
    v___x_1392_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1393_ = l_Lean_Name_num___override(v___x_1392_, v___x_1391_);
    return v___x_1393_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1394_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1395_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1396_ = l_Lean_Name_str___override(v___x_1395_, v___x_1394_);
    return v___x_1396_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_1398_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1399_ = l_Lean_Name_str___override(v___x_1398_, v___x_1397_);
    return v___x_1399_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1402_ = l_Lean_Name_num___override(v___x_1401_, v___x_1400_);
    return v___x_1402_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_;
    v___x_1405_ = 0;
    v___x_1406_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_);
    v___x_1407_ = l_Lean_registerTraceClass(v___x_1404_, v___x_1405_, v___x_1406_);
    return v___x_1407_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2____boxed(
    mut v_a_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
    return v_res_1409_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = crate::leanh::lean_box(0);
    v_dummy_1411_ = l_Lean_Expr_sort___override(v___x_1410_);
    return v_dummy_1411_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(
    mut v_upperBound_1412_: *mut crate::leanh::LeanObject,
    mut v_args_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
    mut v_b_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: u8 = 0;
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1428_ = lean_nat_dec_lt(v_a_1415_, v_upperBound_1412_);
                if v___x_1428_ == 0 {
                    crate::leanh::lean_dec(v_a_1415_);
                    v___x_1429_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_b_1416_);
                    return v___x_1429_;
                } else {
                    v___x_1430_ = crate::leanh::lean_box(0);
                    v___x_1431_ = lean_array_fget_borrowed(v_args_1413_, v_a_1415_);
                    v___x_1434_ = lean_array_get_size(v_a_1414_);
                    v___x_1435_ = lean_nat_dec_lt(v_a_1415_, v___x_1434_);
                    if v___x_1435_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1436_ = lean_array_fget_borrowed(v_a_1414_, v_a_1415_);
                        v___x_1437_ = (crate::leanh::lean_unbox(v___x_1436_) as u8);
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
                v___x_1425_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1426_ = lean_nat_add(v_a_1415_, v___x_1425_);
                crate::leanh::lean_dec(v_a_1415_);
                v_a_1415_ = v___x_1426_;
                v_b_1416_ = v_a_1424_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_1431_);
                v___x_1433_ =
                    l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(
                        v___x_1431_,
                        v___y_1417_,
                        v___y_1418_,
                        v___y_1419_,
                        v___y_1420_,
                        v___y_1421_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1433_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1433_, 1);
                    v_a_1424_ = v___x_1430_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1415_);
                    return v___x_1433_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(
    mut v_x_1438_: *mut crate::leanh::LeanObject,
    mut v_x_1439_: *mut crate::leanh::LeanObject,
    mut v_x_1440_: *mut crate::leanh::LeanObject,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_fn_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1438_) == 5 {
                    v_fn_1475_ = crate::leanh::lean_ctor_get(v_x_1438_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1475_);
                    v_arg_1476_ = crate::leanh::lean_ctor_get(v_x_1438_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1476_);
                    crate::leanh::lean_dec_ref_known(v_x_1438_, 2);
                    v___x_1477_ = lean_array_set(v_x_1439_, v_x_1440_, v_arg_1476_);
                    v___x_1478_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1479_ = lean_nat_sub(v_x_1440_, v___x_1478_);
                    crate::leanh::lean_dec(v_x_1440_);
                    v_x_1438_ = v_fn_1475_;
                    v_x_1439_ = v___x_1477_;
                    v_x_1440_ = v___x_1479_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1440_);
                    if crate::leanh::lean_obj_tag(v_x_1438_) == 4 {
                        v_declName_1481_ = crate::leanh::lean_ctor_get(v_x_1438_, 0);
                        v___x_1482_ = lean_st_ref_take(v___y_1441_);
                        crate::leanh::lean_inc(v_declName_1481_);
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
                if crate::leanh::lean_obj_tag(v___x_1454_) == 0 {
                    v_a_1455_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                    crate::leanh::lean_inc(v_a_1455_);
                    crate::leanh::lean_dec_ref_known(v___x_1454_, 1);
                    v___x_1456_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1457_ = crate::leanh::lean_box(0);
                    v___x_1458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v___x_1453_, v_x_1439_, v_a_1455_, v___x_1456_, v___x_1457_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
                    crate::leanh::lean_dec(v_a_1455_);
                    crate::leanh::lean_dec_ref(v_x_1439_);
                    if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                        v_isSharedCheck_1465_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1458_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v_unused_1466_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                            crate::leanh::lean_dec(v_unused_1466_);
                            v___x_1460_ = v___x_1458_;
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1458_);
                            v___x_1460_ = crate::leanh::lean_box(0);
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1458_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1439_);
                    v_a_1467_ = crate::leanh::lean_ctor_get(v___x_1454_, 0);
                    v_isSharedCheck_1474_ = (!crate::leanh::lean_is_exclusive(v___x_1454_)) as u8;
                    if v_isSharedCheck_1474_ == 0 {
                        v___x_1469_ = v___x_1454_;
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1467_);
                        crate::leanh::lean_dec(v___x_1454_);
                        v___x_1469_ = crate::leanh::lean_box(0);
                        v_isShared_1470_ = v_isSharedCheck_1474_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1457_);
                    v___x_1463_ = v___x_1460_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1457_);
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
                    v_reuseFailAlloc_1473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
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
    mut v_e_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1492_: u8 = 0;
    v___x_1492_ = l_Lean_Expr_isApp(v_e_1485_);
    if v___x_1492_ == 0 {
        let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_1485_);
        v___x_1493_ = crate::leanh::lean_box(0);
        v___x_1494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1493_);
        return v___x_1494_;
    } else {
        let mut v_dummy_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nargs_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_dummy_1495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___closed__0);
        v_nargs_1496_ = l_Lean_Expr_getAppNumArgs(v_e_1485_);
        crate::leanh::lean_inc(v_nargs_1496_);
        v___x_1497_ = lean_mk_array(v_nargs_1496_, v_dummy_1495_);
        v___x_1498_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1499_ = lean_nat_sub(v_nargs_1496_, v___x_1498_);
        crate::leanh::lean_dec(v_nargs_1496_);
        v___x_1500_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_e_1485_, v___x_1497_, v___x_1499_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
        return v___x_1500_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go___boxed(
    mut v_e_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(
        v_e_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_,
    );
    crate::leanh::lean_dec(v_a_1506_);
    crate::leanh::lean_dec_ref(v_a_1505_);
    crate::leanh::lean_dec(v_a_1504_);
    crate::leanh::lean_dec_ref(v_a_1503_);
    crate::leanh::lean_dec(v_a_1502_);
    return v_res_1508_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg___boxed(
    mut v_upperBound_1509_: *mut crate::leanh::LeanObject,
    mut v_args_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_b_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_1509_, v_args_1510_, v_a_1511_, v_a_1512_, v_b_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
    crate::leanh::lean_dec(v___y_1518_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    crate::leanh::lean_dec(v___y_1516_);
    crate::leanh::lean_dec_ref(v___y_1515_);
    crate::leanh::lean_dec(v___y_1514_);
    crate::leanh::lean_dec_ref(v_a_1511_);
    crate::leanh::lean_dec_ref(v_args_1510_);
    crate::leanh::lean_dec(v_upperBound_1509_);
    return v_res_1520_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1___boxed(
    mut v_x_1521_: *mut crate::leanh::LeanObject,
    mut v_x_1522_: *mut crate::leanh::LeanObject,
    mut v_x_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__1(v_x_1521_, v_x_1522_, v_x_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
    crate::leanh::lean_dec(v___y_1528_);
    crate::leanh::lean_dec_ref(v___y_1527_);
    crate::leanh::lean_dec(v___y_1526_);
    crate::leanh::lean_dec_ref(v___y_1525_);
    crate::leanh::lean_dec(v___y_1524_);
    return v_res_1530_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(
    mut v_upperBound_1531_: *mut crate::leanh::LeanObject,
    mut v_args_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
    mut v_inst_1534_: *mut crate::leanh::LeanObject,
    mut v_R_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_b_1537_: *mut crate::leanh::LeanObject,
    mut v_c_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
    mut v___y_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___redArg(v_upperBound_1531_, v_args_1532_, v_a_1533_, v_a_1536_, v_b_1537_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
    return v___x_1545_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0___boxed(
    mut v_upperBound_1546_: *mut crate::leanh::LeanObject,
    mut v_args_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
    mut v_R_1550_: *mut crate::leanh::LeanObject,
    mut v_a_1551_: *mut crate::leanh::LeanObject,
    mut v_b_1552_: *mut crate::leanh::LeanObject,
    mut v_c_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go_spec__0(v_upperBound_1546_, v_args_1547_, v_a_1548_, v_inst_1549_, v_R_1550_, v_a_1551_, v_b_1552_, v_c_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
    crate::leanh::lean_dec(v___y_1558_);
    crate::leanh::lean_dec_ref(v___y_1557_);
    crate::leanh::lean_dec(v___y_1556_);
    crate::leanh::lean_dec_ref(v___y_1555_);
    crate::leanh::lean_dec(v___y_1554_);
    crate::leanh::lean_dec_ref(v_a_1548_);
    crate::leanh::lean_dec_ref(v_args_1547_);
    crate::leanh::lean_dec(v_upperBound_1546_);
    return v_res_1560_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(
    mut v_f_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_unused_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_f_1561_) == 4 {
                    v_declName_1567_ = crate::leanh::lean_ctor_get(v_f_1561_, 0);
                    crate::leanh::lean_inc(v_declName_1567_);
                    crate::leanh::lean_dec_ref_known(v_f_1561_, 2);
                    v___x_1568_ = l_Lean_NameSet_empty;
                    v___x_1569_ = l_Lean_NameSet_insert(v___x_1568_, v_declName_1567_);
                    v___x_1570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1569_);
                    return v___x_1570_;
                } else {
                    v___x_1571_ = l_Lean_NameSet_empty;
                    v___x_1572_ = lean_st_mk_ref(v___x_1571_);
                    v___x_1573_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_go(v_f_1561_, v___x_1572_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
                    if crate::leanh::lean_obj_tag(v___x_1573_) == 0 {
                        v_isSharedCheck_1581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1581_ == 0 {
                            v_unused_1582_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                            crate::leanh::lean_dec(v_unused_1582_);
                            v___x_1575_ = v___x_1573_;
                            v_isShared_1576_ = v_isSharedCheck_1581_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1573_);
                            v___x_1575_ = crate::leanh::lean_box(0);
                            v_isShared_1576_ = v_isSharedCheck_1581_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1572_);
                        v_a_1583_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                        v_isSharedCheck_1590_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1590_ == 0 {
                            v___x_1585_ = v___x_1573_;
                            v_isShared_1586_ = v_isSharedCheck_1590_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1583_);
                            crate::leanh::lean_dec(v___x_1573_);
                            v___x_1585_ = crate::leanh::lean_box(0);
                            v_isShared_1586_ = v_isSharedCheck_1590_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1577_ = lean_st_ref_get(v___x_1572_);
                crate::leanh::lean_dec(v___x_1572_);
                if v_isShared_1576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1575_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
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
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
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
    mut v_f_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ =
        l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(
            v_f_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_,
        );
    crate::leanh::lean_dec(v_a_1595_);
    crate::leanh::lean_dec_ref(v_a_1594_);
    crate::leanh::lean_dec(v_a_1593_);
    crate::leanh::lean_dec_ref(v_a_1592_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(
    mut v_k_1598_: *mut crate::leanh::LeanObject,
    mut v_b_1599_: *mut crate::leanh::LeanObject,
    mut v_c_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1604_);
    crate::leanh::lean_inc_ref(v___y_1603_);
    crate::leanh::lean_inc(v___y_1602_);
    crate::leanh::lean_inc_ref(v___y_1601_);
    v___x_1606_ = crate::leanh::lean_apply_7(
        v_k_1598_,
        v_b_1599_,
        v_c_1600_,
        v___y_1601_,
        v___y_1602_,
        v___y_1603_,
        v___y_1604_,
        crate::leanh::lean_box(0),
    );
    return v___x_1606_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed(
    mut v_k_1607_: *mut crate::leanh::LeanObject,
    mut v_b_1608_: *mut crate::leanh::LeanObject,
    mut v_c_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1615_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0(v_k_1607_, v_b_1608_, v_c_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
    crate::leanh::lean_dec(v___y_1613_);
    crate::leanh::lean_dec_ref(v___y_1612_);
    crate::leanh::lean_dec(v___y_1611_);
    crate::leanh::lean_dec_ref(v___y_1610_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(
    mut v_type_1616_: *mut crate::leanh::LeanObject,
    mut v_k_1617_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1618_: u8,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_a_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1624_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1624_, 0, v_k_1617_);
                v___x_1625_ = 0;
                v___x_1626_ = crate::leanh::lean_box(0);
                v___x_1627_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1635_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1630_ = v___x_1627_;
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1628_);
                        crate::leanh::lean_dec(v___x_1627_);
                        v___x_1630_ = crate::leanh::lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1636_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    v_isSharedCheck_1643_ = (!crate::leanh::lean_is_exclusive(v___x_1627_)) as u8;
                    if v_isSharedCheck_1643_ == 0 {
                        v___x_1638_ = v___x_1627_;
                        v_isShared_1639_ = v_isSharedCheck_1643_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1636_);
                        crate::leanh::lean_dec(v___x_1627_);
                        v___x_1638_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
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
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
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
    mut v_type_1644_: *mut crate::leanh::LeanObject,
    mut v_k_1645_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1652_: u8 = 0;
    let mut v_res_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1652_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1646_) as u8);
    v_res_1653_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_1644_, v_k_1645_, v_cleanupAnnotations_boxed_1652_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
    crate::leanh::lean_dec(v___y_1650_);
    crate::leanh::lean_dec_ref(v___y_1649_);
    crate::leanh::lean_dec(v___y_1648_);
    crate::leanh::lean_dec_ref(v___y_1647_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(
    mut v_00_u03b1_1654_: *mut crate::leanh::LeanObject,
    mut v_type_1655_: *mut crate::leanh::LeanObject,
    mut v_k_1656_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1657_: u8,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_type_1655_, v_k_1656_, v_cleanupAnnotations_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___boxed(
    mut v_00_u03b1_1664_: *mut crate::leanh::LeanObject,
    mut v_type_1665_: *mut crate::leanh::LeanObject,
    mut v_k_1666_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1673_: u8 = 0;
    let mut v_res_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1673_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1667_) as u8);
    v_res_1674_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3(v_00_u03b1_1664_, v_type_1665_, v_k_1666_, v_cleanupAnnotations_boxed_1673_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v___y_1670_);
    crate::leanh::lean_dec(v___y_1669_);
    crate::leanh::lean_dec_ref(v___y_1668_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(
    mut v_msgData_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ = lean_st_ref_get(v___y_1679_);
    v_env_1682_ = crate::leanh::lean_ctor_get(v___x_1681_, 0);
    crate::leanh::lean_inc_ref(v_env_1682_);
    crate::leanh::lean_dec(v___x_1681_);
    v___x_1683_ = lean_st_ref_get(v___y_1677_);
    v_mctx_1684_ = crate::leanh::lean_ctor_get(v___x_1683_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1684_);
    crate::leanh::lean_dec(v___x_1683_);
    v_lctx_1685_ = crate::leanh::lean_ctor_get(v___y_1676_, 2);
    v_options_1686_ = crate::leanh::lean_ctor_get(v___y_1678_, 2);
    crate::leanh::lean_inc_ref(v_options_1686_);
    crate::leanh::lean_inc_ref(v_lctx_1685_);
    v___x_1687_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1687_, 0, v_env_1682_);
    crate::leanh::lean_ctor_set(v___x_1687_, 1, v_mctx_1684_);
    crate::leanh::lean_ctor_set(v___x_1687_, 2, v_lctx_1685_);
    crate::leanh::lean_ctor_set(v___x_1687_, 3, v_options_1686_);
    v___x_1688_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1687_);
    crate::leanh::lean_ctor_set(v___x_1688_, 1, v_msgData_1675_);
    v___x_1689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2___boxed(
    mut v_msgData_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msgData_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    crate::leanh::lean_dec(v___y_1694_);
    crate::leanh::lean_dec_ref(v___y_1693_);
    crate::leanh::lean_dec(v___y_1692_);
    crate::leanh::lean_dec_ref(v___y_1691_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(
    mut v_msg_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1703_ = crate::leanh::lean_ctor_get(v___y_1700_, 5);
                v___x_1704_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
                v_a_1705_ = crate::leanh::lean_ctor_get(v___x_1704_, 0);
                v_isSharedCheck_1713_ = (!crate::leanh::lean_is_exclusive(v___x_1704_)) as u8;
                if v_isSharedCheck_1713_ == 0 {
                    v___x_1707_ = v___x_1704_;
                    v_isShared_1708_ = v_isSharedCheck_1713_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1705_);
                    crate::leanh::lean_dec(v___x_1704_);
                    v___x_1707_ = crate::leanh::lean_box(0);
                    v_isShared_1708_ = v_isSharedCheck_1713_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1703_);
                v___x_1709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1709_, 0, v_ref_1703_);
                crate::leanh::lean_ctor_set(v___x_1709_, 1, v_a_1705_);
                if v_isShared_1708_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1707_, 1);
                    crate::leanh::lean_ctor_set(v___x_1707_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
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
    mut v_msg_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    crate::leanh::lean_dec(v___y_1718_);
    crate::leanh::lean_dec_ref(v___y_1717_);
    crate::leanh::lean_dec(v___y_1716_);
    crate::leanh::lean_dec_ref(v___y_1715_);
    return v_res_1720_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(
    mut v_init_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1722_) == 0 {
                    v_k_1723_ = crate::leanh::lean_ctor_get(v_x_1722_, 1);
                    v_l_1724_ = crate::leanh::lean_ctor_get(v_x_1722_, 3);
                    v_r_1725_ = crate::leanh::lean_ctor_get(v_x_1722_, 4);
                    v___x_1726_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_1721_, v_r_1725_);
                    crate::leanh::lean_inc(v_k_1723_);
                    v___x_1727_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1727_, 0, v_k_1723_);
                    crate::leanh::lean_ctor_set(v___x_1727_, 1, v___x_1726_);
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
    mut v_init_1729_: *mut crate::leanh::LeanObject,
    mut v_x_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v_init_1729_, v_x_1730_);
    crate::leanh::lean_dec(v_x_1730_);
    return v_res_1731_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(
    mut v_a_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1732_) == 0 {
                    v___x_1734_ = l_List_reverse___redArg(v_a_1733_);
                    return v___x_1734_;
                } else {
                    v_head_1735_ = crate::leanh::lean_ctor_get(v_a_1732_, 0);
                    v_tail_1736_ = crate::leanh::lean_ctor_get(v_a_1732_, 1);
                    v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v_a_1732_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1738_ = v_a_1732_;
                        v_isShared_1739_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1736_);
                        crate::leanh::lean_inc(v_head_1735_);
                        crate::leanh::lean_dec(v_a_1732_);
                        v___x_1738_ = crate::leanh::lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1745_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1740_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1740_, 0, v_head_1735_);
                if v_isShared_1739_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1738_, 1, v_a_1733_);
                    crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1740_);
                    v___x_1742_ = v___x_1738_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1733_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__0;
    v___x_1748_ = l_Lean_stringToMessageData(v___x_1747_);
    return v___x_1748_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__2;
    v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
    return v___x_1751_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__6;
    v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0(
    mut v_hasUniverses_1759_: u8,
    mut v_xs_1760_: *mut crate::leanh::LeanObject,
    mut v_type_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
    mut v___y_1764_: *mut crate::leanh::LeanObject,
    mut v___y_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_a_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v___y_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1838_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__5;
                v___x_1825_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1826_ = l_Lean_Expr_isAppOfArity(v_type_1761_, v___x_1824_, v___x_1825_);
                if v___x_1826_ == 0 {
                    v___x_1827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__7);
                    v___x_1828_ = l_Lean_indentExpr(v_type_1761_);
                    v___x_1829_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1827_);
                    crate::leanh::lean_ctor_set(v___x_1829_, 1, v___x_1828_);
                    v___x_1830_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1829_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
                    v_a_1831_ = crate::leanh::lean_ctor_get(v___x_1830_, 0);
                    v_isSharedCheck_1838_ = (!crate::leanh::lean_is_exclusive(v___x_1830_)) as u8;
                    if v_isSharedCheck_1838_ == 0 {
                        v___x_1833_ = v___x_1830_;
                        v_isShared_1834_ = v_isSharedCheck_1838_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1831_);
                        crate::leanh::lean_dec(v___x_1830_);
                        v___x_1833_ = crate::leanh::lean_box(0);
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
                v___x_1769_ = crate::leanh::lean_box(0);
                v___x_1770_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__0(v___x_1769_, v___y_1768_);
                crate::leanh::lean_dec(v___y_1768_);
                v___x_1771_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__1(v___x_1770_, v___x_1769_);
                v___x_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                return v___x_1772_;
            }
            2 => {
                v___x_1778_ = l_Lean_Expr_appArg_x21(v_type_1761_);
                crate::leanh::lean_dec_ref(v_type_1761_);
                v___x_1779_ = l_Lean_Expr_eta(v___x_1778_);
                crate::leanh::lean_inc_ref(v___x_1779_);
                v___x_1780_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_collectFnNames(v___x_1779_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
                if crate::leanh::lean_obj_tag(v___x_1780_) == 0 {
                    v_a_1781_ = crate::leanh::lean_ctor_get(v___x_1780_, 0);
                    crate::leanh::lean_inc(v_a_1781_);
                    crate::leanh::lean_dec_ref_known(v___x_1780_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1781_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_1779_);
                        v___y_1768_ = v_a_1781_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__1);
                        v___x_1783_ = l_Lean_indentExpr(v___x_1779_);
                        v___x_1784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1782_);
                        crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                        v___x_1785_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1784_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
                        v_a_1786_ = crate::leanh::lean_ctor_get(v___x_1785_, 0);
                        v_isSharedCheck_1793_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1785_)) as u8;
                        if v_isSharedCheck_1793_ == 0 {
                            v___x_1788_ = v___x_1785_;
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1786_);
                            crate::leanh::lean_dec(v___x_1785_);
                            v___x_1788_ = crate::leanh::lean_box(0);
                            v_isShared_1789_ = v_isSharedCheck_1793_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1779_);
                    v_a_1794_ = crate::leanh::lean_ctor_get(v___x_1780_, 0);
                    v_isSharedCheck_1801_ = (!crate::leanh::lean_is_exclusive(v___x_1780_)) as u8;
                    if v_isSharedCheck_1801_ == 0 {
                        v___x_1796_ = v___x_1780_;
                        v_isShared_1797_ = v_isSharedCheck_1801_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1794_);
                        crate::leanh::lean_dec(v___x_1780_);
                        v___x_1796_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
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
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
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
                    v___x_1808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___closed__3);
                    v___x_1809_ = l_Lean_indentExpr(v_type_1761_);
                    v___x_1810_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1810_, 0, v___x_1808_);
                    crate::leanh::lean_ctor_set(v___x_1810_, 1, v___x_1809_);
                    v___x_1811_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v___x_1810_, v___y_1805_, v___y_1804_, v___y_1803_, v___y_1806_);
                    v_a_1812_ = crate::leanh::lean_ctor_get(v___x_1811_, 0);
                    v_isSharedCheck_1819_ = (!crate::leanh::lean_is_exclusive(v___x_1811_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1814_ = v___x_1811_;
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1812_);
                        crate::leanh::lean_dec(v___x_1811_);
                        v___x_1814_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
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
                v___x_1822_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_1837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
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
    mut v_hasUniverses_1839_: *mut crate::leanh::LeanObject,
    mut v_xs_1840_: *mut crate::leanh::LeanObject,
    mut v_type_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasUniverses_boxed_1847_: u8 = 0;
    let mut v_res_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hasUniverses_boxed_1847_ = (crate::leanh::lean_unbox(v_hasUniverses_1839_) as u8);
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
    crate::leanh::lean_dec(v___y_1845_);
    crate::leanh::lean_dec_ref(v___y_1844_);
    crate::leanh::lean_dec(v___y_1843_);
    crate::leanh::lean_dec_ref(v___y_1842_);
    crate::leanh::lean_dec_ref(v_xs_1840_);
    return v_res_1848_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
    mut v_proof_1849_: *mut crate::leanh::LeanObject,
    mut v_hasUniverses_1850_: u8,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_1854_);
                crate::leanh::lean_inc_ref(v_a_1853_);
                crate::leanh::lean_inc(v_a_1852_);
                crate::leanh::lean_inc_ref(v_a_1851_);
                v___x_1856_ =
                    lean_infer_type(v_proof_1849_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                if crate::leanh::lean_obj_tag(v___x_1856_) == 0 {
                    v_a_1857_ = crate::leanh::lean_ctor_get(v___x_1856_, 0);
                    crate::leanh::lean_inc(v_a_1857_);
                    crate::leanh::lean_dec_ref_known(v___x_1856_, 1);
                    v___x_1858_ = crate::leanh::lean_box((v_hasUniverses_1850_) as usize);
                    v___f_1859_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___f_1859_, 0, v___x_1858_);
                    v___x_1860_ = 0;
                    v___x_1861_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__3___redArg(v_a_1857_, v___f_1859_, v___x_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                    return v___x_1861_;
                } else {
                    v_a_1862_ = crate::leanh::lean_ctor_get(v___x_1856_, 0);
                    v_isSharedCheck_1869_ = (!crate::leanh::lean_is_exclusive(v___x_1856_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1864_ = v___x_1856_;
                        v_isShared_1865_ = v_isSharedCheck_1869_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1862_);
                        crate::leanh::lean_dec(v___x_1856_);
                        v___x_1864_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
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
    mut v_proof_1870_: *mut crate::leanh::LeanObject,
    mut v_hasUniverses_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hasUniverses_boxed_1877_: u8 = 0;
    let mut v_res_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hasUniverses_boxed_1877_ = (crate::leanh::lean_unbox(v_hasUniverses_1871_) as u8);
    v_res_1878_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
        v_proof_1870_,
        v_hasUniverses_boxed_1877_,
        v_a_1872_,
        v_a_1873_,
        v_a_1874_,
        v_a_1875_,
    );
    crate::leanh::lean_dec(v_a_1875_);
    crate::leanh::lean_dec_ref(v_a_1874_);
    crate::leanh::lean_dec(v_a_1873_);
    crate::leanh::lean_dec_ref(v_a_1872_);
    return v_res_1878_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(
    mut v_00_u03b1_1879_: *mut crate::leanh::LeanObject,
    mut v_msg_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    return v___x_1886_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___boxed(
    mut v_00_u03b1_1887_: *mut crate::leanh::LeanObject,
    mut v_msg_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2(v_00_u03b1_1887_, v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
    crate::leanh::lean_dec(v___y_1892_);
    crate::leanh::lean_dec_ref(v___y_1891_);
    crate::leanh::lean_dec(v___y_1890_);
    crate::leanh::lean_dec_ref(v___y_1889_);
    return v_res_1894_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1902_: u8 = 0;
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_constName_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1895_) == 0 {
                    v___x_1897_ = l_List_reverse___redArg(v_a_1896_);
                    return v___x_1897_;
                } else {
                    v_head_1898_ = crate::leanh::lean_ctor_get(v_a_1895_, 0);
                    v_tail_1899_ = crate::leanh::lean_ctor_get(v_a_1895_, 1);
                    v_isSharedCheck_1911_ = (!crate::leanh::lean_is_exclusive(v_a_1895_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1901_ = v_a_1895_;
                        v_isShared_1902_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1899_);
                        crate::leanh::lean_inc(v_head_1898_);
                        crate::leanh::lean_dec(v_a_1895_);
                        v___x_1901_ = crate::leanh::lean_box(0);
                        v_isShared_1902_ = v_isSharedCheck_1911_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_head_1898_) == 2 {
                    v_constName_1909_ = crate::leanh::lean_ctor_get(v_head_1898_, 0);
                    crate::leanh::lean_inc(v_constName_1909_);
                    crate::leanh::lean_dec_ref_known(v_head_1898_, 1);
                    v___y_1904_ = v_constName_1909_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_head_1898_);
                    v___x_1910_ = crate::leanh::lean_box(0);
                    v___y_1904_ = v___x_1910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1901_, 1, v_a_1896_);
                    crate::leanh::lean_ctor_set(v___x_1901_, 0, v___y_1904_);
                    v___x_1906_ = v___x_1901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___y_1904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1896_);
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
    mut v_s_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = crate::leanh::lean_box(0);
    v___x_1914_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames_spec__0(v_s_1912_, v___x_1913_);
    return v___x_1914_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(
    mut v_a_1915_: *mut crate::leanh::LeanObject,
    mut v_a_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1915_) == 0 {
                    v___x_1917_ = l_List_reverse___redArg(v_a_1916_);
                    return v___x_1917_;
                } else {
                    v_head_1918_ = crate::leanh::lean_ctor_get(v_a_1915_, 0);
                    v_tail_1919_ = crate::leanh::lean_ctor_get(v_a_1915_, 1);
                    v_isSharedCheck_1928_ = (!crate::leanh::lean_is_exclusive(v_a_1915_)) as u8;
                    if v_isSharedCheck_1928_ == 0 {
                        v___x_1921_ = v_a_1915_;
                        v_isShared_1922_ = v_isSharedCheck_1928_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1919_);
                        crate::leanh::lean_inc(v_head_1918_);
                        crate::leanh::lean_dec(v_a_1915_);
                        v___x_1921_ = crate::leanh::lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1928_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1923_ = l_Lean_MessageData_ofName(v_head_1918_);
                if v_isShared_1922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1921_, 1, v_a_1916_);
                    crate::leanh::lean_ctor_set(v___x_1921_, 0, v___x_1923_);
                    v___x_1925_ = v___x_1921_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1916_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1929_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0);
    v___x_1931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1931_, 0, v___x_1930_);
    return v___x_1931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1933_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1934_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1934_, 0, v___x_1933_);
    crate::leanh::lean_ctor_set(v___x_1934_, 1, v___x_1933_);
    crate::leanh::lean_ctor_set(v___x_1934_, 2, v___x_1933_);
    crate::leanh::lean_ctor_set(v___x_1934_, 3, v___x_1933_);
    crate::leanh::lean_ctor_set(v___x_1934_, 4, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1934_, 5, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1934_, 6, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1934_, 7, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1934_, 8, v___x_1932_);
    crate::leanh::lean_ctor_set(v___x_1934_, 9, v___x_1932_);
    return v___x_1934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1936_ = lean_mk_empty_array_with_capacity(v___x_1935_);
    v___x_1937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1937_, 0, v___x_1936_);
    return v___x_1937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1938_: usize = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = 5usize;
    v___x_1939_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1940_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1941_ = lean_mk_empty_array_with_capacity(v___x_1940_);
    v___x_1942_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
    v___x_1943_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1942_);
    crate::leanh::lean_ctor_set(v___x_1943_, 1, v___x_1941_);
    crate::leanh::lean_ctor_set(v___x_1943_, 2, v___x_1939_);
    crate::leanh::lean_ctor_set(v___x_1943_, 3, v___x_1939_);
    crate::leanh::lean_ctor_set_usize(v___x_1943_, 4, v___x_1938_);
    return v___x_1943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1944_ = crate::leanh::lean_box(1);
    v___x_1945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4);
    v___x_1946_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
    v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1947_, 0, v___x_1946_);
    crate::leanh::lean_ctor_set(v___x_1947_, 1, v___x_1945_);
    crate::leanh::lean_ctor_set(v___x_1947_, 2, v___x_1944_);
    return v___x_1947_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1950_ = l_Lean_stringToMessageData(v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1953_ = l_Lean_stringToMessageData(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1959_ = l_Lean_stringToMessageData(v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__14;
    v___x_1962_ = l_Lean_stringToMessageData(v___x_1961_);
    return v___x_1962_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__16;
    v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__18;
    v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1969_: *mut crate::leanh::LeanObject,
    mut v_declHint_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: u8 = 0;
    let mut v_isExporting_1976_: u8 = 0;
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1998_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1973_ = lean_st_ref_get(v___y_1971_);
                v_env_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                crate::leanh::lean_inc_ref(v_env_1974_);
                crate::leanh::lean_dec(v___x_1973_);
                v___x_1975_ = l_Lean_Name_isAnonymous(v_declHint_1970_);
                if v___x_1975_ == 0 {
                    v_isExporting_1976_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1974_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1976_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1974_);
                        crate::leanh::lean_dec(v_declHint_1970_);
                        v___x_1977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1977_, 0, v_msg_1969_);
                        return v___x_1977_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1974_);
                        v___x_1978_ = l_Lean_Environment_setExporting(v_env_1974_, v___x_1975_);
                        crate::leanh::lean_inc(v_declHint_1970_);
                        crate::leanh::lean_inc_ref(v___x_1978_);
                        v___x_1979_ = l_Lean_Environment_contains(
                            v___x_1978_,
                            v_declHint_1970_,
                            v_isExporting_1976_,
                        );
                        if v___x_1979_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1978_);
                            crate::leanh::lean_dec_ref(v_env_1974_);
                            crate::leanh::lean_dec(v_declHint_1970_);
                            v___x_1980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1980_, 0, v_msg_1969_);
                            return v___x_1980_;
                        } else {
                            v___x_1981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2);
                            v___x_1982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                            v___x_1983_ = l_Lean_Options_empty;
                            v___x_1984_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1984_, 0, v___x_1978_);
                            crate::leanh::lean_ctor_set(v___x_1984_, 1, v___x_1981_);
                            crate::leanh::lean_ctor_set(v___x_1984_, 2, v___x_1982_);
                            crate::leanh::lean_ctor_set(v___x_1984_, 3, v___x_1983_);
                            crate::leanh::lean_inc(v_declHint_1970_);
                            v___x_1985_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1970_, v___x_1975_);
                            v_c_1986_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1986_, 0, v___x_1984_);
                            crate::leanh::lean_ctor_set(v_c_1986_, 1, v___x_1985_);
                            v___x_1987_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1974_,
                                v_declHint_1970_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1987_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1974_);
                                crate::leanh::lean_dec(v_declHint_1970_);
                                v___x_1988_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                                v___x_1989_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
                                crate::leanh::lean_ctor_set(v___x_1989_, 1, v_c_1986_);
                                v___x_1990_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                                v___x_1991_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_1989_);
                                crate::leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                                v___x_1992_ = l_Lean_MessageData_note(v___x_1991_);
                                v___x_1993_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1993_, 0, v_msg_1969_);
                                crate::leanh::lean_ctor_set(v___x_1993_, 1, v___x_1992_);
                                v___x_1994_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1993_);
                                return v___x_1994_;
                            } else {
                                v_val_1995_ = crate::leanh::lean_ctor_get(v___x_1987_, 0);
                                v_isSharedCheck_2030_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1987_)) as u8;
                                if v_isSharedCheck_2030_ == 0 {
                                    v___x_1997_ = v___x_1987_;
                                    v_isShared_1998_ = v_isSharedCheck_2030_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1995_);
                                    crate::leanh::lean_dec(v___x_1987_);
                                    v___x_1997_ = crate::leanh::lean_box(0);
                                    v_isShared_1998_ = v_isSharedCheck_2030_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1974_);
                    crate::leanh::lean_dec(v_declHint_1970_);
                    v___x_2031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v_msg_1969_);
                    return v___x_2031_;
                }
            }
            1 => {
                v___x_1999_ = crate::leanh::lean_box(0);
                v___x_2000_ = l_Lean_Environment_header(v_env_1974_);
                crate::leanh::lean_dec_ref(v_env_1974_);
                v___x_2001_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2000_);
                v_mod_2002_ = lean_array_get(v___x_1999_, v___x_2001_, v_val_1995_);
                crate::leanh::lean_dec(v_val_1995_);
                crate::leanh::lean_dec_ref(v___x_2001_);
                v___x_2003_ = l_Lean_isPrivateName(v_declHint_1970_);
                crate::leanh::lean_dec(v_declHint_1970_);
                if v___x_2003_ == 0 {
                    v___x_2004_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_2005_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_2004_);
                    crate::leanh::lean_ctor_set(v___x_2005_, 1, v_c_1986_);
                    v___x_2006_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_2007_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2007_, 0, v___x_2005_);
                    crate::leanh::lean_ctor_set(v___x_2007_, 1, v___x_2006_);
                    v___x_2008_ = l_Lean_MessageData_ofName(v_mod_2002_);
                    v___x_2009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2007_);
                    crate::leanh::lean_ctor_set(v___x_2009_, 1, v___x_2008_);
                    v___x_2010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__15);
                    v___x_2011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2011_, 0, v___x_2009_);
                    crate::leanh::lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                    v___x_2012_ = l_Lean_MessageData_note(v___x_2011_);
                    v___x_2013_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2013_, 0, v_msg_1969_);
                    crate::leanh::lean_ctor_set(v___x_2013_, 1, v___x_2012_);
                    if v_isShared_1998_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1997_, 0);
                        crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_2013_);
                        v___x_2015_ = v___x_1997_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
                        v___x_2015_ = v_reuseFailAlloc_2016_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2017_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_2018_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v_c_1986_);
                    v___x_2019_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__17);
                    v___x_2020_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_2018_);
                    crate::leanh::lean_ctor_set(v___x_2020_, 1, v___x_2019_);
                    v___x_2021_ = l_Lean_MessageData_ofName(v_mod_2002_);
                    v___x_2022_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2020_);
                    crate::leanh::lean_ctor_set(v___x_2022_, 1, v___x_2021_);
                    v___x_2023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__19);
                    v___x_2024_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2022_);
                    crate::leanh::lean_ctor_set(v___x_2024_, 1, v___x_2023_);
                    v___x_2025_ = l_Lean_MessageData_note(v___x_2024_);
                    v___x_2026_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2026_, 0, v_msg_1969_);
                    crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2025_);
                    if v_isShared_1998_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1997_, 0);
                        crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_2026_);
                        v___x_2028_ = v___x_1997_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
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
    mut v_msg_2032_: *mut crate::leanh::LeanObject,
    mut v_declHint_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2032_, v_declHint_2033_, v___y_2034_);
    crate::leanh::lean_dec(v___y_2034_);
    return v_res_2036_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_2037_: *mut crate::leanh::LeanObject,
    mut v_declHint_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2044_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2037_, v_declHint_2038_, v___y_2042_);
                v_a_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                v_isSharedCheck_2054_ = (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                if v_isSharedCheck_2054_ == 0 {
                    v___x_2047_ = v___x_2044_;
                    v_isShared_2048_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2045_);
                    crate::leanh::lean_dec(v___x_2044_);
                    v___x_2047_ = crate::leanh::lean_box(0);
                    v_isShared_2048_ = v_isSharedCheck_2054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2049_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2050_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2049_);
                crate::leanh::lean_ctor_set(v___x_2050_, 1, v_a_2045_);
                if v_isShared_2048_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2047_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
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
    mut v_msg_2055_: *mut crate::leanh::LeanObject,
    mut v_declHint_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
    mut v___y_2058_: *mut crate::leanh::LeanObject,
    mut v___y_2059_: *mut crate::leanh::LeanObject,
    mut v___y_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2055_, v_declHint_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
    crate::leanh::lean_dec(v___y_2060_);
    crate::leanh::lean_dec_ref(v___y_2059_);
    crate::leanh::lean_dec(v___y_2058_);
    crate::leanh::lean_dec_ref(v___y_2057_);
    return v_res_2062_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_2063_: *mut crate::leanh::LeanObject,
    mut v_msg_2064_: *mut crate::leanh::LeanObject,
    mut v___y_2065_: *mut crate::leanh::LeanObject,
    mut v___y_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2082_: u8 = 0;
    let mut v_cancelTk_x3f_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2084_: u8 = 0;
    let mut v_inheritedTraceOptions_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2070_ = crate::leanh::lean_ctor_get(v___y_2067_, 0);
    v_fileMap_2071_ = crate::leanh::lean_ctor_get(v___y_2067_, 1);
    v_options_2072_ = crate::leanh::lean_ctor_get(v___y_2067_, 2);
    v_currRecDepth_2073_ = crate::leanh::lean_ctor_get(v___y_2067_, 3);
    v_maxRecDepth_2074_ = crate::leanh::lean_ctor_get(v___y_2067_, 4);
    v_ref_2075_ = crate::leanh::lean_ctor_get(v___y_2067_, 5);
    v_currNamespace_2076_ = crate::leanh::lean_ctor_get(v___y_2067_, 6);
    v_openDecls_2077_ = crate::leanh::lean_ctor_get(v___y_2067_, 7);
    v_initHeartbeats_2078_ = crate::leanh::lean_ctor_get(v___y_2067_, 8);
    v_maxHeartbeats_2079_ = crate::leanh::lean_ctor_get(v___y_2067_, 9);
    v_quotContext_2080_ = crate::leanh::lean_ctor_get(v___y_2067_, 10);
    v_currMacroScope_2081_ = crate::leanh::lean_ctor_get(v___y_2067_, 11);
    v_diag_2082_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2067_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2083_ = crate::leanh::lean_ctor_get(v___y_2067_, 12);
    v_suppressElabErrors_2084_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2067_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2085_ = crate::leanh::lean_ctor_get(v___y_2067_, 13);
    v_ref_2086_ = l_Lean_replaceRef(v_ref_2063_, v_ref_2075_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2085_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2083_);
    crate::leanh::lean_inc(v_currMacroScope_2081_);
    crate::leanh::lean_inc(v_quotContext_2080_);
    crate::leanh::lean_inc(v_maxHeartbeats_2079_);
    crate::leanh::lean_inc(v_initHeartbeats_2078_);
    crate::leanh::lean_inc(v_openDecls_2077_);
    crate::leanh::lean_inc(v_currNamespace_2076_);
    crate::leanh::lean_inc(v_maxRecDepth_2074_);
    crate::leanh::lean_inc(v_currRecDepth_2073_);
    crate::leanh::lean_inc_ref(v_options_2072_);
    crate::leanh::lean_inc_ref(v_fileMap_2071_);
    crate::leanh::lean_inc_ref(v_fileName_2070_);
    v___x_2087_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2087_, 0, v_fileName_2070_);
    crate::leanh::lean_ctor_set(v___x_2087_, 1, v_fileMap_2071_);
    crate::leanh::lean_ctor_set(v___x_2087_, 2, v_options_2072_);
    crate::leanh::lean_ctor_set(v___x_2087_, 3, v_currRecDepth_2073_);
    crate::leanh::lean_ctor_set(v___x_2087_, 4, v_maxRecDepth_2074_);
    crate::leanh::lean_ctor_set(v___x_2087_, 5, v_ref_2086_);
    crate::leanh::lean_ctor_set(v___x_2087_, 6, v_currNamespace_2076_);
    crate::leanh::lean_ctor_set(v___x_2087_, 7, v_openDecls_2077_);
    crate::leanh::lean_ctor_set(v___x_2087_, 8, v_initHeartbeats_2078_);
    crate::leanh::lean_ctor_set(v___x_2087_, 9, v_maxHeartbeats_2079_);
    crate::leanh::lean_ctor_set(v___x_2087_, 10, v_quotContext_2080_);
    crate::leanh::lean_ctor_set(v___x_2087_, 11, v_currMacroScope_2081_);
    crate::leanh::lean_ctor_set(v___x_2087_, 12, v_cancelTk_x3f_2083_);
    crate::leanh::lean_ctor_set(v___x_2087_, 13, v_inheritedTraceOptions_2085_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2087_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2082_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2087_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2084_,
    );
    v___x_2088_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2___redArg(v_msg_2064_, v___y_2065_, v___y_2066_, v___x_2087_, v___y_2068_);
    crate::leanh::lean_dec_ref_known(v___x_2087_, 14);
    return v___x_2088_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_2089_: *mut crate::leanh::LeanObject,
    mut v_msg_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2089_, v_msg_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
    crate::leanh::lean_dec(v___y_2094_);
    crate::leanh::lean_dec_ref(v___y_2093_);
    crate::leanh::lean_dec(v___y_2092_);
    crate::leanh::lean_dec_ref(v___y_2091_);
    crate::leanh::lean_dec(v_ref_2089_);
    return v_res_2096_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_2097_: *mut crate::leanh::LeanObject,
    mut v_msg_2098_: *mut crate::leanh::LeanObject,
    mut v_declHint_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_2098_, v_declHint_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
    v_a_2106_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
    crate::leanh::lean_inc(v_a_2106_);
    crate::leanh::lean_dec_ref(v___x_2105_);
    v___x_2107_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2097_, v_a_2106_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
    return v___x_2107_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_2108_: *mut crate::leanh::LeanObject,
    mut v_msg_2109_: *mut crate::leanh::LeanObject,
    mut v_declHint_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
    mut v___y_2115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2116_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2108_, v_msg_2109_, v_declHint_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
    crate::leanh::lean_dec(v___y_2114_);
    crate::leanh::lean_dec_ref(v___y_2113_);
    crate::leanh::lean_dec(v___y_2112_);
    crate::leanh::lean_dec_ref(v___y_2111_);
    crate::leanh::lean_dec(v_ref_2108_);
    return v_res_2116_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
    return v___x_2119_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
    return v___x_2122_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2123_: *mut crate::leanh::LeanObject,
    mut v_constName_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2131_ = 0;
    crate::leanh::lean_inc(v_constName_2124_);
    v___x_2132_ = l_Lean_MessageData_ofConstName(v_constName_2124_, v___x_2131_);
    v___x_2133_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2130_);
    crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
    v___x_2134_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2135_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2133_);
    crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
    v___x_2136_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2123_, v___x_2135_, v_constName_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2137_: *mut crate::leanh::LeanObject,
    mut v_constName_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2144_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2137_, v_constName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
    crate::leanh::lean_dec(v___y_2142_);
    crate::leanh::lean_dec_ref(v___y_2141_);
    crate::leanh::lean_dec(v___y_2140_);
    crate::leanh::lean_dec_ref(v___y_2139_);
    crate::leanh::lean_dec(v_ref_2137_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(
    mut v_constName_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2151_ = crate::leanh::lean_ctor_get(v___y_2148_, 5);
    v___x_2152_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2151_, v_constName_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
    return v___x_2152_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg___boxed(
    mut v_constName_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    crate::leanh::lean_dec(v___y_2157_);
    crate::leanh::lean_dec_ref(v___y_2156_);
    crate::leanh::lean_dec(v___y_2155_);
    crate::leanh::lean_dec_ref(v___y_2154_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
    mut v_constName_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2174_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = lean_st_ref_get(v___y_2164_);
                v_env_2167_ = crate::leanh::lean_ctor_get(v___x_2166_, 0);
                crate::leanh::lean_inc_ref(v_env_2167_);
                crate::leanh::lean_dec(v___x_2166_);
                v___x_2168_ = 0;
                crate::leanh::lean_inc(v_constName_2160_);
                v___x_2169_ =
                    l_Lean_Environment_find_x3f(v_env_2167_, v_constName_2160_, v___x_2168_);
                if crate::leanh::lean_obj_tag(v___x_2169_) == 0 {
                    v___x_2170_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
                    return v___x_2170_;
                } else {
                    crate::leanh::lean_dec(v_constName_2160_);
                    v_val_2171_ = crate::leanh::lean_ctor_get(v___x_2169_, 0);
                    v_isSharedCheck_2178_ = (!crate::leanh::lean_is_exclusive(v___x_2169_)) as u8;
                    if v_isSharedCheck_2178_ == 0 {
                        v___x_2173_ = v___x_2169_;
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2171_);
                        crate::leanh::lean_dec(v___x_2169_);
                        v___x_2173_ = crate::leanh::lean_box(0);
                        v_isShared_2174_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2174_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2173_, 0);
                    v___x_2176_ = v___x_2173_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2171_);
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
    mut v_constName_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
        v_constName_2179_,
        v___y_2180_,
        v___y_2181_,
        v___y_2182_,
        v___y_2183_,
    );
    crate::leanh::lean_dec(v___y_2183_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    crate::leanh::lean_dec(v___y_2181_);
    crate::leanh::lean_dec_ref(v___y_2180_);
    return v_res_2185_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0()
-> f64 {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: f64 = 0.0;
    v___x_2186_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2187_ = lean_float_of_nat(v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
    mut v_cls_2191_: *mut crate::leanh::LeanObject,
    mut v_msg_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
    mut v___y_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v_tid_2217_: u64 = 0;
    let mut v_traces_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: f64 = 0.0;
    let mut v___x_2224_: u8 = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2198_ = crate::leanh::lean_ctor_get(v___y_2195_, 5);
                v___x_2199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols_spec__2_spec__2(v_msg_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
                v_a_2200_ = crate::leanh::lean_ctor_get(v___x_2199_, 0);
                v_isSharedCheck_2244_ = (!crate::leanh::lean_is_exclusive(v___x_2199_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2202_ = v___x_2199_;
                    v_isShared_2203_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2200_);
                    crate::leanh::lean_dec(v___x_2199_);
                    v___x_2202_ = crate::leanh::lean_box(0);
                    v_isShared_2203_ = v_isSharedCheck_2244_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2204_ = lean_st_ref_take(v___y_2196_);
                v_traceState_2205_ = crate::leanh::lean_ctor_get(v___x_2204_, 4);
                v_env_2206_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                v_nextMacroScope_2207_ = crate::leanh::lean_ctor_get(v___x_2204_, 1);
                v_ngen_2208_ = crate::leanh::lean_ctor_get(v___x_2204_, 2);
                v_auxDeclNGen_2209_ = crate::leanh::lean_ctor_get(v___x_2204_, 3);
                v_cache_2210_ = crate::leanh::lean_ctor_get(v___x_2204_, 5);
                v_messages_2211_ = crate::leanh::lean_ctor_get(v___x_2204_, 6);
                v_infoState_2212_ = crate::leanh::lean_ctor_get(v___x_2204_, 7);
                v_snapshotTasks_2213_ = crate::leanh::lean_ctor_get(v___x_2204_, 8);
                v_isSharedCheck_2243_ = (!crate::leanh::lean_is_exclusive(v___x_2204_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2215_ = v___x_2204_;
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2213_);
                    crate::leanh::lean_inc(v_infoState_2212_);
                    crate::leanh::lean_inc(v_messages_2211_);
                    crate::leanh::lean_inc(v_cache_2210_);
                    crate::leanh::lean_inc(v_traceState_2205_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2209_);
                    crate::leanh::lean_inc(v_ngen_2208_);
                    crate::leanh::lean_inc(v_nextMacroScope_2207_);
                    crate::leanh::lean_inc(v_env_2206_);
                    crate::leanh::lean_dec(v___x_2204_);
                    v___x_2215_ = crate::leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2217_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2205_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2218_ = crate::leanh::lean_ctor_get(v_traceState_2205_, 0);
                v_isSharedCheck_2242_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2205_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v___x_2220_ = v_traceState_2205_;
                    v_isShared_2221_ = v_isSharedCheck_2242_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2218_);
                    crate::leanh::lean_dec(v_traceState_2205_);
                    v___x_2220_ = crate::leanh::lean_box(0);
                    v_isShared_2221_ = v_isSharedCheck_2242_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2222_ = crate::leanh::lean_box(0);
                v___x_2223_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__0);
                v___x_2224_ = 0;
                v___x_2225_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__1;
                v___x_2226_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2226_, 0, v_cls_2191_);
                crate::leanh::lean_ctor_set(v___x_2226_, 1, v___x_2222_);
                crate::leanh::lean_ctor_set(v___x_2226_, 2, v___x_2225_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2223_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2223_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2224_,
                );
                v___x_2227_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2___closed__2;
                v___x_2228_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2226_);
                crate::leanh::lean_ctor_set(v___x_2228_, 1, v_a_2200_);
                crate::leanh::lean_ctor_set(v___x_2228_, 2, v___x_2227_);
                crate::leanh::lean_inc(v_ref_2198_);
                v___x_2229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2229_, 0, v_ref_2198_);
                crate::leanh::lean_ctor_set(v___x_2229_, 1, v___x_2228_);
                v___x_2230_ = l_Lean_PersistentArray_push___redArg(v_traces_2218_, v___x_2229_);
                if v_isShared_2221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2230_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2217_,
                    );
                    v___x_2232_ = v_reuseFailAlloc_2241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2215_, 4, v___x_2232_);
                    v___x_2234_ = v___x_2215_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_env_2206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_nextMacroScope_2207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_ngen_2208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 3, v_auxDeclNGen_2209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 4, v___x_2232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 5, v_cache_2210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 6, v_messages_2211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 7, v_infoState_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 8, v_snapshotTasks_2213_);
                    v___x_2234_ = v_reuseFailAlloc_2240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2235_ = lean_st_ref_set(v___y_2196_, v___x_2234_);
                v___x_2236_ = crate::leanh::lean_box(0);
                if v_isShared_2203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2202_, 0, v___x_2236_);
                    v___x_2238_ = v___x_2202_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
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
    mut v_cls_2245_: *mut crate::leanh::LeanObject,
    mut v_msg_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
        v_cls_2245_,
        v_msg_2246_,
        v___y_2247_,
        v___y_2248_,
        v___y_2249_,
        v___y_2250_,
    );
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec_ref(v___y_2249_);
    crate::leanh::lean_dec(v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2247_);
    return v_res_2252_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2258_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
    v___x_2259_ = l_Lean_Meta_Grind_mkInjectiveTheorem___closed__2;
    v___x_2260_ = l_Lean_Name_append(v___x_2259_, v___x_2258_);
    return v___x_2260_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2262_ = l_Lean_Meta_Grind_mkInjectiveTheorem___closed__4;
    v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lean_Meta_Grind_mkInjectiveTheorem(
    mut v_declName_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2276_: u8 = 0;
    let mut v___y_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2289_: u8 = 0;
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_a_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2316_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: u8 = 0;
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_a_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_2264_);
                v___x_2270_ =
                    l_Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0(
                        v_declName_2264_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2270_) == 0 {
                    v_a_2271_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                    crate::leanh::lean_inc(v_a_2271_);
                    crate::leanh::lean_dec_ref_known(v___x_2270_, 1);
                    crate::leanh::lean_inc(v_declName_2264_);
                    v___x_2272_ = l_Lean_Meta_Grind_getProofForDecl(
                        v_declName_2264_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2272_) == 0 {
                        v_a_2273_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                        v_isSharedCheck_2325_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2272_)) as u8;
                        if v_isSharedCheck_2325_ == 0 {
                            v___x_2275_ = v___x_2272_;
                            v_isShared_2276_ = v_isSharedCheck_2325_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2273_);
                            crate::leanh::lean_dec(v___x_2272_);
                            v___x_2275_ = crate::leanh::lean_box(0);
                            v_isShared_2276_ = v_isSharedCheck_2325_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2271_);
                        crate::leanh::lean_dec(v_declName_2264_);
                        v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                        v_isSharedCheck_2333_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2272_)) as u8;
                        if v_isSharedCheck_2333_ == 0 {
                            v___x_2328_ = v___x_2272_;
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2326_);
                            crate::leanh::lean_dec(v___x_2272_);
                            v___x_2328_ = crate::leanh::lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2264_);
                    v_a_2334_ = crate::leanh::lean_ctor_get(v___x_2270_, 0);
                    v_isSharedCheck_2341_ = (!crate::leanh::lean_is_exclusive(v___x_2270_)) as u8;
                    if v_isSharedCheck_2341_ == 0 {
                        v___x_2336_ = v___x_2270_;
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2334_);
                        crate::leanh::lean_dec(v___x_2270_);
                        v___x_2336_ = crate::leanh::lean_box(0);
                        v_isShared_2337_ = v_isSharedCheck_2341_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2321_ = l_Lean_ConstantInfo_levelParams(v_a_2271_);
                crate::leanh::lean_dec(v_a_2271_);
                v___x_2322_ = l_List_isEmpty___redArg(v___x_2321_);
                crate::leanh::lean_dec(v___x_2321_);
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
                v___x_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2280_, 0, v_declName_2264_);
                v___x_2281_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2281_, 0, v___x_2279_);
                crate::leanh::lean_ctor_set(v___x_2281_, 1, v_a_2273_);
                crate::leanh::lean_ctor_set(v___x_2281_, 2, v___y_2278_);
                crate::leanh::lean_ctor_set(v___x_2281_, 3, v___x_2280_);
                if v_isShared_2276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2275_, 0, v___x_2281_);
                    v___x_2283_ = v___x_2275_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
                    v___x_2283_ = v_reuseFailAlloc_2284_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2283_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_2273_);
                v___x_2287_ =
                    l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_getSymbols(
                        v_a_2273_,
                        v___y_2286_,
                        v_a_2265_,
                        v_a_2266_,
                        v_a_2267_,
                        v_a_2268_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2287_) == 0 {
                    v_options_2288_ = crate::leanh::lean_ctor_get(v_a_2267_, 2);
                    v_hasTrace_2289_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2288_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2289_ == 0 {
                        v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                        crate::leanh::lean_inc(v_a_2290_);
                        crate::leanh::lean_dec_ref_known(v___x_2287_, 1);
                        v___y_2278_ = v_a_2290_;
                        state = 2;
                        continue;
                    } else {
                        v_a_2291_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                        crate::leanh::lean_inc(v_a_2291_);
                        crate::leanh::lean_dec_ref_known(v___x_2287_, 1);
                        v_inheritedTraceOptions_2292_ = crate::leanh::lean_ctor_get(v_a_2267_, 13);
                        v___x_2293_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_;
                        v___x_2294_ = crate::leanh::lean_obj_once(
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
                            crate::leanh::lean_inc(v_declName_2264_);
                            v___x_2296_ = l_Lean_MessageData_ofName(v_declName_2264_);
                            v___x_2297_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5_once
                                ),
                                _init_l_Lean_Meta_Grind_mkInjectiveTheorem___closed__5,
                            );
                            v___x_2298_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2298_, 0, v___x_2296_);
                            crate::leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
                            crate::leanh::lean_inc(v_a_2291_);
                            v___x_2299_ = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_symbolsToNames(v_a_2291_);
                            v___x_2300_ = crate::leanh::lean_box(0);
                            v___x_2301_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__1(v___x_2299_, v___x_2300_);
                            v___x_2302_ = l_Lean_MessageData_ofList(v___x_2301_);
                            v___x_2303_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2298_);
                            crate::leanh::lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                            v___x_2304_ =
                                l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__2(
                                    v___x_2293_,
                                    v___x_2303_,
                                    v_a_2265_,
                                    v_a_2266_,
                                    v_a_2267_,
                                    v_a_2268_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_2304_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2304_, 1);
                                v___y_2278_ = v_a_2291_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_2291_);
                                crate::leanh::lean_del_object(v___x_2275_);
                                crate::leanh::lean_dec(v_a_2273_);
                                crate::leanh::lean_dec(v_declName_2264_);
                                v_a_2305_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                                v_isSharedCheck_2312_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2304_)) as u8;
                                if v_isSharedCheck_2312_ == 0 {
                                    v___x_2307_ = v___x_2304_;
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2305_);
                                    crate::leanh::lean_dec(v___x_2304_);
                                    v___x_2307_ = crate::leanh::lean_box(0);
                                    v_isShared_2308_ = v_isSharedCheck_2312_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2275_);
                    crate::leanh::lean_dec(v_a_2273_);
                    crate::leanh::lean_dec(v_declName_2264_);
                    v_a_2313_ = crate::leanh::lean_ctor_get(v___x_2287_, 0);
                    v_isSharedCheck_2320_ = (!crate::leanh::lean_is_exclusive(v___x_2287_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2315_ = v___x_2287_;
                        v_isShared_2316_ = v_isSharedCheck_2320_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2313_);
                        crate::leanh::lean_dec(v___x_2287_);
                        v___x_2315_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
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
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
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
                    v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
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
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
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
    mut v_declName_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2348_ = l_Lean_Meta_Grind_mkInjectiveTheorem(
        v_declName_2342_,
        v_a_2343_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
    );
    crate::leanh::lean_dec(v_a_2346_);
    crate::leanh::lean_dec_ref(v_a_2345_);
    crate::leanh::lean_dec(v_a_2344_);
    crate::leanh::lean_dec_ref(v_a_2343_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(
    mut v_00_u03b1_2349_: *mut crate::leanh::LeanObject,
    mut v_constName_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___redArg(v_constName_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0___boxed(
    mut v_00_u03b1_2357_: *mut crate::leanh::LeanObject,
    mut v_constName_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0(v_00_u03b1_2357_, v_constName_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
    crate::leanh::lean_dec(v___y_2362_);
    crate::leanh::lean_dec_ref(v___y_2361_);
    crate::leanh::lean_dec(v___y_2360_);
    crate::leanh::lean_dec_ref(v___y_2359_);
    return v_res_2364_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2365_: *mut crate::leanh::LeanObject,
    mut v_ref_2366_: *mut crate::leanh::LeanObject,
    mut v_constName_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2373_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___redArg(v_ref_2366_, v_constName_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
    return v___x_2373_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2374_: *mut crate::leanh::LeanObject,
    mut v_ref_2375_: *mut crate::leanh::LeanObject,
    mut v_constName_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1(v_00_u03b1_2374_, v_ref_2375_, v_constName_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
    crate::leanh::lean_dec(v___y_2380_);
    crate::leanh::lean_dec_ref(v___y_2379_);
    crate::leanh::lean_dec(v___y_2378_);
    crate::leanh::lean_dec_ref(v___y_2377_);
    crate::leanh::lean_dec(v_ref_2375_);
    return v_res_2382_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_2383_: *mut crate::leanh::LeanObject,
    mut v_ref_2384_: *mut crate::leanh::LeanObject,
    mut v_msg_2385_: *mut crate::leanh::LeanObject,
    mut v_declHint_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2384_, v_msg_2385_, v_declHint_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_2393_: *mut crate::leanh::LeanObject,
    mut v_ref_2394_: *mut crate::leanh::LeanObject,
    mut v_msg_2395_: *mut crate::leanh::LeanObject,
    mut v_declHint_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2393_, v_ref_2394_, v_msg_2395_, v_declHint_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
    crate::leanh::lean_dec(v___y_2400_);
    crate::leanh::lean_dec_ref(v___y_2399_);
    crate::leanh::lean_dec(v___y_2398_);
    crate::leanh::lean_dec_ref(v___y_2397_);
    crate::leanh::lean_dec(v_ref_2394_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_2403_: *mut crate::leanh::LeanObject,
    mut v_declHint_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_2403_, v_declHint_2404_, v___y_2408_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_2411_: *mut crate::leanh::LeanObject,
    mut v_declHint_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
    mut v___y_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_2411_, v_declHint_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
    crate::leanh::lean_dec(v___y_2416_);
    crate::leanh::lean_dec_ref(v___y_2415_);
    crate::leanh::lean_dec(v___y_2414_);
    crate::leanh::lean_dec_ref(v___y_2413_);
    return v_res_2418_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_2419_: *mut crate::leanh::LeanObject,
    mut v_ref_2420_: *mut crate::leanh::LeanObject,
    mut v_msg_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2420_, v_msg_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
    return v___x_2427_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_2428_: *mut crate::leanh::LeanObject,
    mut v_ref_2429_: *mut crate::leanh::LeanObject,
    mut v_msg_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_mkInjectiveTheorem_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2428_, v_ref_2429_, v_msg_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    crate::leanh::lean_dec(v___y_2432_);
    crate::leanh::lean_dec_ref(v___y_2431_);
    crate::leanh::lean_dec(v_ref_2429_);
    return v_res_2436_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2437_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__0);
    v___x_2439_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
    v___x_2441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2441_, 0, v___x_2440_);
    crate::leanh::lean_ctor_set(v___x_2441_, 1, v___x_2440_);
    return v___x_2441_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__1);
    v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 1, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 2, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 3, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 4, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2443_, 5, v___x_2442_);
    return v___x_2443_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(
    mut v_ext_2444_: *mut crate::leanh::LeanObject,
    mut v_b_2445_: *mut crate::leanh::LeanObject,
    mut v_kind_2446_: u8,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_unused_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_unused_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_2451_ = crate::leanh::lean_ctor_get(v___y_2448_, 6);
                v___x_2452_ = lean_st_ref_take(v___y_2449_);
                v_env_2453_ = crate::leanh::lean_ctor_get(v___x_2452_, 0);
                v_nextMacroScope_2454_ = crate::leanh::lean_ctor_get(v___x_2452_, 1);
                v_ngen_2455_ = crate::leanh::lean_ctor_get(v___x_2452_, 2);
                v_auxDeclNGen_2456_ = crate::leanh::lean_ctor_get(v___x_2452_, 3);
                v_traceState_2457_ = crate::leanh::lean_ctor_get(v___x_2452_, 4);
                v_messages_2458_ = crate::leanh::lean_ctor_get(v___x_2452_, 6);
                v_infoState_2459_ = crate::leanh::lean_ctor_get(v___x_2452_, 7);
                v_snapshotTasks_2460_ = crate::leanh::lean_ctor_get(v___x_2452_, 8);
                v_isSharedCheck_2487_ = (!crate::leanh::lean_is_exclusive(v___x_2452_)) as u8;
                if v_isSharedCheck_2487_ == 0 {
                    v_unused_2488_ = crate::leanh::lean_ctor_get(v___x_2452_, 5);
                    crate::leanh::lean_dec(v_unused_2488_);
                    v___x_2462_ = v___x_2452_;
                    v_isShared_2463_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2460_);
                    crate::leanh::lean_inc(v_infoState_2459_);
                    crate::leanh::lean_inc(v_messages_2458_);
                    crate::leanh::lean_inc(v_traceState_2457_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2456_);
                    crate::leanh::lean_inc(v_ngen_2455_);
                    crate::leanh::lean_inc(v_nextMacroScope_2454_);
                    crate::leanh::lean_inc(v_env_2453_);
                    crate::leanh::lean_dec(v___x_2452_);
                    v___x_2462_ = crate::leanh::lean_box(0);
                    v_isShared_2463_ = v_isSharedCheck_2487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_currNamespace_2451_);
                v___x_2464_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_2453_,
                    v_ext_2444_,
                    v_b_2445_,
                    v_kind_2446_,
                    v_currNamespace_2451_,
                );
                v___x_2465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__2);
                if v_isShared_2463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2462_, 5, v___x_2465_);
                    crate::leanh::lean_ctor_set(v___x_2462_, 0, v___x_2464_);
                    v___x_2467_ = v___x_2462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_nextMacroScope_2454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_ngen_2455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_auxDeclNGen_2456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_traceState_2457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 5, v___x_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 6, v_messages_2458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 7, v_infoState_2459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 8, v_snapshotTasks_2460_);
                    v___x_2467_ = v_reuseFailAlloc_2486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2468_ = lean_st_ref_set(v___y_2449_, v___x_2467_);
                v___x_2469_ = lean_st_ref_take(v___y_2447_);
                v_mctx_2470_ = crate::leanh::lean_ctor_get(v___x_2469_, 0);
                v_zetaDeltaFVarIds_2471_ = crate::leanh::lean_ctor_get(v___x_2469_, 2);
                v_postponed_2472_ = crate::leanh::lean_ctor_get(v___x_2469_, 3);
                v_diag_2473_ = crate::leanh::lean_ctor_get(v___x_2469_, 4);
                v_isSharedCheck_2484_ = (!crate::leanh::lean_is_exclusive(v___x_2469_)) as u8;
                if v_isSharedCheck_2484_ == 0 {
                    v_unused_2485_ = crate::leanh::lean_ctor_get(v___x_2469_, 1);
                    crate::leanh::lean_dec(v_unused_2485_);
                    v___x_2475_ = v___x_2469_;
                    v_isShared_2476_ = v_isSharedCheck_2484_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2473_);
                    crate::leanh::lean_inc(v_postponed_2472_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2471_);
                    crate::leanh::lean_inc(v_mctx_2470_);
                    crate::leanh::lean_dec(v___x_2469_);
                    v___x_2475_ = crate::leanh::lean_box(0);
                    v_isShared_2476_ = v_isSharedCheck_2484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___closed__3);
                if v_isShared_2476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2475_, 1, v___x_2477_);
                    v___x_2479_ = v___x_2475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_mctx_2470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2477_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2483_,
                        2,
                        v_zetaDeltaFVarIds_2471_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_postponed_2472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_diag_2473_);
                    v___x_2479_ = v_reuseFailAlloc_2483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2480_ = lean_st_ref_set(v___y_2447_, v___x_2479_);
                v___x_2481_ = crate::leanh::lean_box(0);
                v___x_2482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2482_, 0, v___x_2481_);
                return v___x_2482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg___boxed(
    mut v_ext_2489_: *mut crate::leanh::LeanObject,
    mut v_b_2490_: *mut crate::leanh::LeanObject,
    mut v_kind_2491_: *mut crate::leanh::LeanObject,
    mut v___y_2492_: *mut crate::leanh::LeanObject,
    mut v___y_2493_: *mut crate::leanh::LeanObject,
    mut v___y_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2496_: u8 = 0;
    let mut v_res_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2496_ = (crate::leanh::lean_unbox(v_kind_2491_) as u8);
    v_res_2497_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2489_, v_b_2490_, v_kind_boxed_2496_, v___y_2492_, v___y_2493_, v___y_2494_);
    crate::leanh::lean_dec(v___y_2494_);
    crate::leanh::lean_dec_ref(v___y_2493_);
    crate::leanh::lean_dec(v___y_2492_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0(
    mut v_00_u03b1_2498_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2499_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2500_: *mut crate::leanh::LeanObject,
    mut v_ext_2501_: *mut crate::leanh::LeanObject,
    mut v_b_2502_: *mut crate::leanh::LeanObject,
    mut v_kind_2503_: u8,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
    mut v___y_2506_: *mut crate::leanh::LeanObject,
    mut v___y_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2501_, v_b_2502_, v_kind_2503_, v___y_2505_, v___y_2506_, v___y_2507_);
    return v___x_2509_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___boxed(
    mut v_00_u03b1_2510_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2511_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2512_: *mut crate::leanh::LeanObject,
    mut v_ext_2513_: *mut crate::leanh::LeanObject,
    mut v_b_2514_: *mut crate::leanh::LeanObject,
    mut v_kind_2515_: *mut crate::leanh::LeanObject,
    mut v___y_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2521_: u8 = 0;
    let mut v_res_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2521_ = (crate::leanh::lean_unbox(v_kind_2515_) as u8);
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
    crate::leanh::lean_dec(v___y_2519_);
    crate::leanh::lean_dec_ref(v___y_2518_);
    crate::leanh::lean_dec(v___y_2517_);
    crate::leanh::lean_dec_ref(v___y_2516_);
    return v_res_2522_;
}
pub unsafe fn l_Lean_Meta_Grind_Extension_addInjectiveAttr(
    mut v_ext_2523_: *mut crate::leanh::LeanObject,
    mut v_declName_2524_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2525_: u8,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v_a_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_2531_) == 0 {
                    v_a_2532_ = crate::leanh::lean_ctor_get(v___x_2531_, 0);
                    crate::leanh::lean_inc(v_a_2532_);
                    crate::leanh::lean_dec_ref_known(v___x_2531_, 1);
                    v___x_2533_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2533_, 0, v_a_2532_);
                    v___x_2534_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Grind_Extension_addInjectiveAttr_spec__0___redArg(v_ext_2523_, v___x_2533_, v_attrKind_2525_, v_a_2527_, v_a_2528_, v_a_2529_);
                    return v___x_2534_;
                } else {
                    crate::leanh::lean_dec_ref(v_ext_2523_);
                    v_a_2535_ = crate::leanh::lean_ctor_get(v___x_2531_, 0);
                    v_isSharedCheck_2542_ = (!crate::leanh::lean_is_exclusive(v___x_2531_)) as u8;
                    if v_isSharedCheck_2542_ == 0 {
                        v___x_2537_ = v___x_2531_;
                        v_isShared_2538_ = v_isSharedCheck_2542_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2535_);
                        crate::leanh::lean_dec(v___x_2531_);
                        v___x_2537_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
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
    mut v_ext_2543_: *mut crate::leanh::LeanObject,
    mut v_declName_2544_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_attrKind_boxed_2551_: u8 = 0;
    let mut v_res_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_2551_ = (crate::leanh::lean_unbox(v_attrKind_2545_) as u8);
    v_res_2552_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(
        v_ext_2543_,
        v_declName_2544_,
        v_attrKind_boxed_2551_,
        v_a_2546_,
        v_a_2547_,
        v_a_2548_,
        v_a_2549_,
    );
    crate::leanh::lean_dec(v_a_2549_);
    crate::leanh::lean_dec_ref(v_a_2548_);
    crate::leanh::lean_dec(v_a_2547_);
    crate::leanh::lean_dec_ref(v_a_2546_);
    return v_res_2552_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Injective(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3173337487____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_1215188614____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_Injective_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Injective_3941467707____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Injective(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Injective(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
}
