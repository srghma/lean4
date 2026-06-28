// Lean compiler output
// Module: Lean.Elab.Tactic.Split
// Imports: Lean.Meta.Tactic.Split Lean.Elab.Tactic.Location
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getId, l_Lean_Syntax_isIdent,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isStr;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_getFVarId;
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_getAppFn, l_Lean_Expr_isAppOf,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_findFromUserName_x3f, l_Lean_LocalDecl_toExpr,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_hint_x27, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_nil, l_Lean_MessageData_note, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_inlineExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_FVarId_getType___redArg, l_Lean_MessageData_ofLazyM};
use crate::r#gen::Lean::Meta::Hint::l_Lean_MessageData_hint;
use crate::r#gen::Lean::Meta::Tactic::Split::{
    initialize_Lean_Meta_Tactic_Split, l_Lean_Meta_splitLocalDecl_x3f, l_Lean_Meta_splitTarget_x3f,
    runtime_initialize_Lean_Meta_Tactic_Split,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getNondepPropHyps, l_Lean_MVarId_getType, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::Structure::{l_Lean_getStructureFields, l_Lean_isStructure};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value: crate::leanh::LeanStringObject<87> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [85, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 116, 114, 97, 99, 101, 46, 115, 112, 108, 105, 116, 46, 102, 97, 105, 108, 117, 114, 101, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 100, 105, 115, 112, 108, 97, 121, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 97, 105, 108, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut crate::leanh::LeanObject,13219768312984610626 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value) as *mut crate::leanh::LeanObject,8171071557273278778 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16145843736367156323 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut crate::leanh::LeanObject,1731991885970815592 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,1767494567867404924 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 72, 121, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value) as *mut crate::leanh::LeanObject,12722427251967365861 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [84, 111, 32, 97, 112, 112, 108, 121, 32, 96, 115, 112, 108, 105, 116, 96, 32, 97, 116, 32, 116, 104, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 44, 32, 117, 115, 101, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 115, 112, 108, 105, 116, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 83, 112, 101, 99, 105, 102, 121, 105, 110, 103, 32, 97, 32, 116, 101, 114, 109, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 121, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 115, 112, 108, 105, 116, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 83, 112, 101, 99, 105, 102, 121, 105, 110, 103, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [41, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value: crate::leanh::LeanStringObject<112> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 112, m_capacity: 112, m_length: 111, m_data: [83, 112, 101, 99, 105, 102, 121, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 116, 111, 32, 115, 112, 108, 105, 116, 44, 32, 111, 114, 32, 117, 115, 101, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 42, 96, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 116, 97, 114, 103, 101, 116, 32, 116, 104, 97, 116, 32, 99, 97, 110, 32, 98, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 104, 101, 32, 103, 111, 97, 108, 32, 97, 110, 100, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [73, 102, 32, 121, 111, 117, 32, 109, 101, 97, 110, 116, 32, 116, 111, 32, 100, 101, 115, 116, 114, 117, 99, 116, 32, 116, 104, 105, 115, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [44, 32, 117, 115, 101, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 96, 32, 116, 97, 99, 116, 105, 99, 32, 105, 110, 115, 116, 101, 97, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,9743492140944907313 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,15289851429949568889 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 105, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 106, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut crate::leanh::LeanObject,18188493160499796729 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 97, 110, 32, 96, 105, 102, 96, 32, 111, 114, 32, 96, 109, 97, 116, 99, 104, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value: crate::leanh::LeanStringObject<58> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 97, 110, 32, 96, 105, 102, 96, 32, 111, 114, 32, 96, 109, 97, 116, 99, 104, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value: crate::leanh::LeanStringObject<187> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 187, m_capacity: 187, m_length: 186, m_data: [96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 42, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 97, 116, 116, 101, 109, 112, 116, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 97, 116, 32, 110, 111, 110, 45, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 111, 114, 32, 116, 104, 111, 115, 101, 32, 111, 110, 32, 119, 104, 105, 99, 104, 32, 111, 116, 104, 101, 114, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 100, 101, 112, 101, 110, 100, 46, 32, 73, 116, 32, 109, 97, 121, 32, 115, 116, 105, 108, 108, 32, 98, 101, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 109, 97, 110, 117, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 32, 97, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 117, 115, 105, 110, 103, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value: crate::leanh::LeanStringObject<89> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 103, 111, 97, 108, 44, 32, 97, 110, 100, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 116, 104, 97, 116, 32, 99, 111, 117, 108, 100, 32, 98, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 32, 119, 101, 114, 101, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 111, 114, 32, 97, 110, 121, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalSplit___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalSplit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSplit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSplit___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 83, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value) as *mut crate::leanh::LeanObject,6451815636812638566 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(
    mut v_k_1285_: *mut crate::leanh::LeanObject,
    mut v_defValue_1286_: u8,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v_v_1298_: u8 = 0;
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1289_ = crate::leanh::lean_ctor_get(v___y_1287_, 2);
                v_map_1290_ = crate::leanh::lean_ctor_get(v_options_1289_, 0);
                v___x_1291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1290_, v_k_1285_);
                if crate::leanh::lean_obj_tag(v___x_1291_) == 0 {
                    v___x_1292_ = crate::leanh::lean_box((v_defValue_1286_) as usize);
                    v___x_1293_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1292_);
                    return v___x_1293_;
                } else {
                    v_val_1294_ = crate::leanh::lean_ctor_get(v___x_1291_, 0);
                    v_isSharedCheck_1307_ = (!crate::leanh::lean_is_exclusive(v___x_1291_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1296_ = v___x_1291_;
                        v_isShared_1297_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1294_);
                        crate::leanh::lean_dec(v___x_1291_);
                        v___x_1296_ = crate::leanh::lean_box(0);
                        v_isShared_1297_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_1294_) == 1 {
                    v_v_1298_ = crate::leanh::lean_ctor_get_uint8(v_val_1294_, 0 as u32);
                    crate::leanh::lean_dec_ref_known(v_val_1294_, 0);
                    v___x_1299_ = crate::leanh::lean_box((v_v_1298_) as usize);
                    if v_isShared_1297_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1296_, 0);
                        crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1299_);
                        v___x_1301_ = v___x_1296_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
                        v___x_1301_ = v_reuseFailAlloc_1302_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_1294_);
                    v___x_1303_ = crate::leanh::lean_box((v_defValue_1286_) as usize);
                    if v_isShared_1297_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1296_, 0);
                        crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1303_);
                        v___x_1305_ = v___x_1296_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
                        v___x_1305_ = v_reuseFailAlloc_1306_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1301_;
            }
            3 => {
                return v___x_1305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg___boxed(
    mut v_k_1308_: *mut crate::leanh::LeanObject,
    mut v_defValue_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_boxed_1312_: u8 = 0;
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_1312_ = (crate::leanh::lean_unbox(v_defValue_1309_) as u8);
    v_res_1313_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_1308_, v_defValue_boxed_1312_, v___y_1310_);
    crate::leanh::lean_dec_ref(v___y_1310_);
    crate::leanh::lean_dec(v_k_1308_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(
    mut v_k_1314_: *mut crate::leanh::LeanObject,
    mut v_defValue_1315_: u8,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
    mut v___y_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_1314_, v_defValue_1315_, v___y_1318_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___boxed(
    mut v_k_1322_: *mut crate::leanh::LeanObject,
    mut v_defValue_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_defValue_boxed_1329_ = (crate::leanh::lean_unbox(v_defValue_1323_) as u8);
    v_res_1330_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(v_k_1322_, v_defValue_boxed_1329_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
    crate::leanh::lean_dec(v___y_1327_);
    crate::leanh::lean_dec_ref(v___y_1326_);
    crate::leanh::lean_dec(v___y_1325_);
    crate::leanh::lean_dec_ref(v___y_1324_);
    crate::leanh::lean_dec(v_k_1322_);
    return v_res_1330_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0;
    v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1334_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1);
    v___x_1335_ = l_Lean_MessageData_hint_x27(v___x_1334_);
    return v___x_1335_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(
    mut v___x_1336_: *mut crate::leanh::LeanObject,
    mut v___x_1337_: u8,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1343_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v___x_1336_, v___x_1337_, v___y_1340_);
                v_a_1344_ = crate::leanh::lean_ctor_get(v___x_1343_, 0);
                v_isSharedCheck_1357_ = (!crate::leanh::lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1357_ == 0 {
                    v___x_1346_ = v___x_1343_;
                    v_isShared_1347_ = v_isSharedCheck_1357_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1344_);
                    crate::leanh::lean_dec(v___x_1343_);
                    v___x_1346_ = crate::leanh::lean_box(0);
                    v_isShared_1347_ = v_isSharedCheck_1357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1348_ = (crate::leanh::lean_unbox(v_a_1344_) as u8);
                crate::leanh::lean_dec(v_a_1344_);
                if v___x_1348_ == 0 {
                    v___x_1349_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2);
                    if v_isShared_1347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1349_);
                        v___x_1351_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
                        v___x_1351_ = v_reuseFailAlloc_1352_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1353_ = l_Lean_MessageData_nil;
                    if v_isShared_1347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1353_);
                        v___x_1355_ = v___x_1346_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
                        v___x_1355_ = v_reuseFailAlloc_1356_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1351_;
            }
            3 => {
                return v___x_1355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed(
    mut v___x_1358_: *mut crate::leanh::LeanObject,
    mut v___x_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_689__boxed_1365_: u8 = 0;
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_689__boxed_1365_ = (crate::leanh::lean_unbox(v___x_1359_) as u8);
    v_res_1366_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(
            v___x_1358_,
            v___x_689__boxed_1365_,
            v___y_1360_,
            v___y_1361_,
            v___y_1362_,
            v___y_1363_,
        );
    crate::leanh::lean_dec(v___y_1363_);
    crate::leanh::lean_dec_ref(v___y_1362_);
    crate::leanh::lean_dec(v___y_1361_);
    crate::leanh::lean_dec_ref(v___y_1360_);
    crate::leanh::lean_dec(v___x_1358_);
    return v_res_1366_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5;
    v___f_1381_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4;
    v___x_1382_ = l_Lean_MessageData_ofLazyM(v___f_1381_, v___x_1380_);
    return v___x_1382_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1383_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6);
    return v___x_1383_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(
    mut v_msgData_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_st_ref_get(v___y_1388_);
    v_env_1391_ = crate::leanh::lean_ctor_get(v___x_1390_, 0);
    crate::leanh::lean_inc_ref(v_env_1391_);
    crate::leanh::lean_dec(v___x_1390_);
    v___x_1392_ = lean_st_ref_get(v___y_1386_);
    v_mctx_1393_ = crate::leanh::lean_ctor_get(v___x_1392_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1393_);
    crate::leanh::lean_dec(v___x_1392_);
    v_lctx_1394_ = crate::leanh::lean_ctor_get(v___y_1385_, 2);
    v_options_1395_ = crate::leanh::lean_ctor_get(v___y_1387_, 2);
    crate::leanh::lean_inc_ref(v_options_1395_);
    crate::leanh::lean_inc_ref(v_lctx_1394_);
    v___x_1396_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1396_, 0, v_env_1391_);
    crate::leanh::lean_ctor_set(v___x_1396_, 1, v_mctx_1393_);
    crate::leanh::lean_ctor_set(v___x_1396_, 2, v_lctx_1394_);
    crate::leanh::lean_ctor_set(v___x_1396_, 3, v_options_1395_);
    v___x_1397_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1397_, 0, v___x_1396_);
    crate::leanh::lean_ctor_set(v___x_1397_, 1, v_msgData_1384_);
    v___x_1398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1397_);
    return v___x_1398_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
    mut v___y_1403_: *mut crate::leanh::LeanObject,
    mut v___y_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
    crate::leanh::lean_dec(v___y_1403_);
    crate::leanh::lean_dec_ref(v___y_1402_);
    crate::leanh::lean_dec(v___y_1401_);
    crate::leanh::lean_dec_ref(v___y_1400_);
    return v_res_1405_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(
    mut v_msg_1406_: *mut crate::leanh::LeanObject,
    mut v___y_1407_: *mut crate::leanh::LeanObject,
    mut v___y_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1412_ = crate::leanh::lean_ctor_get(v___y_1409_, 5);
                v___x_1413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
                v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                if v_isSharedCheck_1422_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1414_);
                    crate::leanh::lean_dec(v___x_1413_);
                    v___x_1416_ = crate::leanh::lean_box(0);
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1412_);
                v___x_1418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1418_, 0, v_ref_1412_);
                crate::leanh::lean_ctor_set(v___x_1418_, 1, v_a_1414_);
                if v_isShared_1417_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1416_, 1);
                    crate::leanh::lean_ctor_set(v___x_1416_, 0, v___x_1418_);
                    v___x_1420_ = v___x_1416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(
    mut v_msg_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
    mut v___y_1425_: *mut crate::leanh::LeanObject,
    mut v___y_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
    crate::leanh::lean_dec(v___y_1427_);
    crate::leanh::lean_dec_ref(v___y_1426_);
    crate::leanh::lean_dec(v___y_1425_);
    crate::leanh::lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(
    mut v_ref_1430_: *mut crate::leanh::LeanObject,
    mut v_msg_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1453_: u8 = 0;
    let mut v_cancelTk_x3f_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1455_: u8 = 0;
    let mut v_inheritedTraceOptions_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1441_ = crate::leanh::lean_ctor_get(v___y_1438_, 0);
    v_fileMap_1442_ = crate::leanh::lean_ctor_get(v___y_1438_, 1);
    v_options_1443_ = crate::leanh::lean_ctor_get(v___y_1438_, 2);
    v_currRecDepth_1444_ = crate::leanh::lean_ctor_get(v___y_1438_, 3);
    v_maxRecDepth_1445_ = crate::leanh::lean_ctor_get(v___y_1438_, 4);
    v_ref_1446_ = crate::leanh::lean_ctor_get(v___y_1438_, 5);
    v_currNamespace_1447_ = crate::leanh::lean_ctor_get(v___y_1438_, 6);
    v_openDecls_1448_ = crate::leanh::lean_ctor_get(v___y_1438_, 7);
    v_initHeartbeats_1449_ = crate::leanh::lean_ctor_get(v___y_1438_, 8);
    v_maxHeartbeats_1450_ = crate::leanh::lean_ctor_get(v___y_1438_, 9);
    v_quotContext_1451_ = crate::leanh::lean_ctor_get(v___y_1438_, 10);
    v_currMacroScope_1452_ = crate::leanh::lean_ctor_get(v___y_1438_, 11);
    v_diag_1453_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1438_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1454_ = crate::leanh::lean_ctor_get(v___y_1438_, 12);
    v_suppressElabErrors_1455_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1438_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1456_ = crate::leanh::lean_ctor_get(v___y_1438_, 13);
    v_ref_1457_ = l_Lean_replaceRef(v_ref_1430_, v_ref_1446_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1456_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1454_);
    crate::leanh::lean_inc(v_currMacroScope_1452_);
    crate::leanh::lean_inc(v_quotContext_1451_);
    crate::leanh::lean_inc(v_maxHeartbeats_1450_);
    crate::leanh::lean_inc(v_initHeartbeats_1449_);
    crate::leanh::lean_inc(v_openDecls_1448_);
    crate::leanh::lean_inc(v_currNamespace_1447_);
    crate::leanh::lean_inc(v_maxRecDepth_1445_);
    crate::leanh::lean_inc(v_currRecDepth_1444_);
    crate::leanh::lean_inc_ref(v_options_1443_);
    crate::leanh::lean_inc_ref(v_fileMap_1442_);
    crate::leanh::lean_inc_ref(v_fileName_1441_);
    v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1458_, 0, v_fileName_1441_);
    crate::leanh::lean_ctor_set(v___x_1458_, 1, v_fileMap_1442_);
    crate::leanh::lean_ctor_set(v___x_1458_, 2, v_options_1443_);
    crate::leanh::lean_ctor_set(v___x_1458_, 3, v_currRecDepth_1444_);
    crate::leanh::lean_ctor_set(v___x_1458_, 4, v_maxRecDepth_1445_);
    crate::leanh::lean_ctor_set(v___x_1458_, 5, v_ref_1457_);
    crate::leanh::lean_ctor_set(v___x_1458_, 6, v_currNamespace_1447_);
    crate::leanh::lean_ctor_set(v___x_1458_, 7, v_openDecls_1448_);
    crate::leanh::lean_ctor_set(v___x_1458_, 8, v_initHeartbeats_1449_);
    crate::leanh::lean_ctor_set(v___x_1458_, 9, v_maxHeartbeats_1450_);
    crate::leanh::lean_ctor_set(v___x_1458_, 10, v_quotContext_1451_);
    crate::leanh::lean_ctor_set(v___x_1458_, 11, v_currMacroScope_1452_);
    crate::leanh::lean_ctor_set(v___x_1458_, 12, v_cancelTk_x3f_1454_);
    crate::leanh::lean_ctor_set(v___x_1458_, 13, v_inheritedTraceOptions_1456_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1458_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1453_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1458_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1455_,
    );
    v___x_1459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1431_, v___y_1436_, v___y_1437_, v___x_1458_, v___y_1439_);
    crate::leanh::lean_dec_ref_known(v___x_1458_, 14);
    return v___x_1459_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(
    mut v_ref_1460_: *mut crate::leanh::LeanObject,
    mut v_msg_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
    mut v___y_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_1460_, v_msg_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
    crate::leanh::lean_dec(v___y_1469_);
    crate::leanh::lean_dec_ref(v___y_1468_);
    crate::leanh::lean_dec(v___y_1467_);
    crate::leanh::lean_dec_ref(v___y_1466_);
    crate::leanh::lean_dec(v___y_1465_);
    crate::leanh::lean_dec_ref(v___y_1464_);
    crate::leanh::lean_dec(v___y_1463_);
    crate::leanh::lean_dec_ref(v___y_1462_);
    crate::leanh::lean_dec(v_ref_1460_);
    return v_res_1471_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1486_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1486_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1501_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14;
    v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
    return v___x_1502_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1504_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16;
    v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
    return v___x_1505_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18;
    v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(
    mut v___x_1509_: u8,
    mut v_t_1510_: *mut crate::leanh::LeanObject,
    mut v_error_1511_: *mut crate::leanh::LeanObject,
    mut v_loc_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: u8 = 0;
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1509_ == 0 {
                    v___x_1522_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                    return v___x_1522_;
                } else {
                    v_lctx_1523_ = crate::leanh::lean_ctor_get(v___y_1517_, 2);
                    v_name_1524_ = l_Lean_Syntax_getId(v_t_1510_);
                    v___x_1580_ = l_Lean_Name_isStr(v_name_1524_);
                    if v___x_1580_ == 0 {
                        v___y_1526_ = v___x_1580_;
                        state = 1;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v_loc_1512_) == 0 {
                            v___y_1526_ = v___x_1580_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_name_1524_);
                            v___x_1581_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                            return v___x_1581_;
                        }
                    }
                }
            }
            1 => {
                if v___y_1526_ == 0 {
                    crate::leanh::lean_dec(v_name_1524_);
                    v___x_1527_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                    return v___x_1527_;
                } else {
                    v___x_1528_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1523_, v_name_1524_);
                    if crate::leanh::lean_obj_tag(v___x_1528_) == 1 {
                        v_val_1529_ = crate::leanh::lean_ctor_get(v___x_1528_, 0);
                        crate::leanh::lean_inc(v_val_1529_);
                        crate::leanh::lean_dec_ref_known(v___x_1528_, 1);
                        v_ref_1530_ = crate::leanh::lean_ctor_get(v___y_1519_, 5);
                        v___x_1531_ = l_Lean_LocalDecl_toExpr(v_val_1529_);
                        v___x_1532_ = 0;
                        v___x_1533_ = l_Lean_SourceInfo_fromRef(v_ref_1530_, v___x_1532_);
                        v___x_1534_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1;
                        v___x_1535_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1;
                        v___x_1536_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
                        crate::leanh::lean_inc_n(v___x_1533_, 7);
                        v___x_1537_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1533_);
                        crate::leanh::lean_ctor_set(v___x_1537_, 1, v___x_1535_);
                        v___x_1538_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7;
                        v___x_1539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
                        v___x_1540_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1533_);
                        crate::leanh::lean_ctor_set(v___x_1540_, 1, v___x_1538_);
                        crate::leanh::lean_ctor_set(v___x_1540_, 2, v___x_1539_);
                        v___x_1541_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10;
                        v___x_1542_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11;
                        v___x_1543_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1533_);
                        crate::leanh::lean_ctor_set(v___x_1543_, 1, v___x_1542_);
                        v___x_1544_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13;
                        v___x_1545_ = lean_mk_syntax_ident(v_name_1524_);
                        v___x_1546_ = l_Lean_Syntax_node1(v___x_1533_, v___x_1538_, v___x_1545_);
                        v___x_1547_ = l_Lean_Syntax_node1(v___x_1533_, v___x_1544_, v___x_1546_);
                        v___x_1548_ =
                            l_Lean_Syntax_node2(v___x_1533_, v___x_1541_, v___x_1543_, v___x_1547_);
                        v___x_1549_ = l_Lean_Syntax_node1(v___x_1533_, v___x_1538_, v___x_1548_);
                        v___x_1550_ = l_Lean_Syntax_node3(
                            v___x_1533_,
                            v___x_1536_,
                            v___x_1537_,
                            v___x_1540_,
                            v___x_1549_,
                        );
                        v___x_1551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
                        v___x_1552_ = l_Lean_MessageData_ofExpr(v___x_1531_);
                        crate::leanh::lean_inc_ref(v___x_1552_);
                        v___x_1553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1553_, 0, v___x_1551_);
                        crate::leanh::lean_ctor_set(v___x_1553_, 1, v___x_1552_);
                        v___x_1554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
                        v___x_1555_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1555_, 0, v___x_1553_);
                        crate::leanh::lean_ctor_set(v___x_1555_, 1, v___x_1554_);
                        v___x_1556_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                        crate::leanh::lean_ctor_set(v___x_1556_, 1, v___x_1552_);
                        v___x_1557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
                        v___x_1558_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                        crate::leanh::lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                        v___x_1559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1559_, 0, v___x_1534_);
                        crate::leanh::lean_ctor_set(v___x_1559_, 1, v___x_1550_);
                        v___x_1560_ = crate::leanh::lean_box(0);
                        v___x_1561_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1559_);
                        crate::leanh::lean_ctor_set(v___x_1561_, 1, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1561_, 2, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1561_, 3, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1561_, 4, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1561_, 5, v___x_1560_);
                        v___x_1562_ = 0;
                        v___x_1563_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1563_, 0, v___x_1561_);
                        crate::leanh::lean_ctor_set(v___x_1563_, 1, v___x_1560_);
                        crate::leanh::lean_ctor_set(v___x_1563_, 2, v___x_1560_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1563_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v___x_1562_,
                        );
                        v___x_1564_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1565_ = lean_mk_empty_array_with_capacity(v___x_1564_);
                        v___x_1566_ = lean_array_push(v___x_1565_, v___x_1563_);
                        v___x_1567_ = l_Lean_MessageData_hint(
                            v___x_1558_,
                            v___x_1566_,
                            v___x_1560_,
                            v___x_1560_,
                            v___x_1532_,
                            v___y_1519_,
                            v___y_1520_,
                        );
                        crate::leanh::lean_dec_ref(v___x_1566_);
                        if crate::leanh::lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1568_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                            crate::leanh::lean_inc(v_a_1568_);
                            crate::leanh::lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1569_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1569_, 0, v_error_1511_);
                            crate::leanh::lean_ctor_set(v___x_1569_, 1, v_a_1568_);
                            v___x_1570_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v___x_1569_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                            return v___x_1570_;
                        } else {
                            crate::leanh::lean_dec_ref(v_error_1511_);
                            v_a_1571_ = crate::leanh::lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1578_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1578_ == 0 {
                                v___x_1573_ = v___x_1567_;
                                v_isShared_1574_ = v_isSharedCheck_1578_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1571_);
                                crate::leanh::lean_dec(v___x_1567_);
                                v___x_1573_ = crate::leanh::lean_box(0);
                                v_isShared_1574_ = v_isSharedCheck_1578_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1528_);
                        crate::leanh::lean_dec(v_name_1524_);
                        v___x_1579_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                        return v___x_1579_;
                    }
                }
            }
            2 => {
                if v_isShared_1574_ == 0 {
                    v___x_1576_ = v___x_1573_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(
    mut v___x_1582_: *mut crate::leanh::LeanObject,
    mut v_t_1583_: *mut crate::leanh::LeanObject,
    mut v_error_1584_: *mut crate::leanh::LeanObject,
    mut v_loc_1585_: *mut crate::leanh::LeanObject,
    mut v___y_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
    mut v___y_1591_: *mut crate::leanh::LeanObject,
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6770__boxed_1595_: u8 = 0;
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6770__boxed_1595_ = (crate::leanh::lean_unbox(v___x_1582_) as u8);
    v_res_1596_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6770__boxed_1595_, v_t_1583_, v_error_1584_, v_loc_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
    crate::leanh::lean_dec(v___y_1593_);
    crate::leanh::lean_dec_ref(v___y_1592_);
    crate::leanh::lean_dec(v___y_1591_);
    crate::leanh::lean_dec_ref(v___y_1590_);
    crate::leanh::lean_dec(v___y_1589_);
    crate::leanh::lean_dec_ref(v___y_1588_);
    crate::leanh::lean_dec(v___y_1587_);
    crate::leanh::lean_dec_ref(v___y_1586_);
    crate::leanh::lean_dec(v_loc_1585_);
    crate::leanh::lean_dec(v_t_1583_);
    return v_res_1596_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_error_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0;
    v_error_1599_ = l_Lean_stringToMessageData(v___x_1598_);
    return v_error_1599_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(
    mut v_t_1600_: *mut crate::leanh::LeanObject,
    mut v_loc_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
    mut v_a_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
    mut v_a_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
    mut v_a_1607_: *mut crate::leanh::LeanObject,
    mut v_a_1608_: *mut crate::leanh::LeanObject,
    mut v_a_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_error_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_error_1611_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
    v___x_1612_ = l_Lean_Syntax_isIdent(v_t_1600_);
    v___x_1613_ = crate::leanh::lean_box((v___x_1612_) as usize);
    v___y_1614_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
    crate::leanh::lean_closure_set(v___y_1614_, 0, v___x_1613_);
    crate::leanh::lean_closure_set(v___y_1614_, 1, v_t_1600_);
    crate::leanh::lean_closure_set(v___y_1614_, 2, v_error_1611_);
    crate::leanh::lean_closure_set(v___y_1614_, 3, v_loc_1601_);
    v___x_1615_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_1614_,
        v_a_1602_,
        v_a_1603_,
        v_a_1604_,
        v_a_1605_,
        v_a_1606_,
        v_a_1607_,
        v_a_1608_,
        v_a_1609_,
    );
    return v___x_1615_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___boxed(
    mut v_t_1616_: *mut crate::leanh::LeanObject,
    mut v_loc_1617_: *mut crate::leanh::LeanObject,
    mut v_a_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
    mut v_a_1620_: *mut crate::leanh::LeanObject,
    mut v_a_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_a_1624_: *mut crate::leanh::LeanObject,
    mut v_a_1625_: *mut crate::leanh::LeanObject,
    mut v_a_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(
            v_t_1616_,
            v_loc_1617_,
            v_a_1618_,
            v_a_1619_,
            v_a_1620_,
            v_a_1621_,
            v_a_1622_,
            v_a_1623_,
            v_a_1624_,
            v_a_1625_,
        );
    crate::leanh::lean_dec(v_a_1625_);
    crate::leanh::lean_dec_ref(v_a_1624_);
    crate::leanh::lean_dec(v_a_1623_);
    crate::leanh::lean_dec_ref(v_a_1622_);
    crate::leanh::lean_dec(v_a_1621_);
    crate::leanh::lean_dec_ref(v_a_1620_);
    crate::leanh::lean_dec(v_a_1619_);
    crate::leanh::lean_dec_ref(v_a_1618_);
    return v_res_1627_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(
    mut v_00_u03b1_1628_: *mut crate::leanh::LeanObject,
    mut v_ref_1629_: *mut crate::leanh::LeanObject,
    mut v_msg_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
    mut v___y_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_1629_, v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(
    mut v_00_u03b1_1641_: *mut crate::leanh::LeanObject,
    mut v_ref_1642_: *mut crate::leanh::LeanObject,
    mut v_msg_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1653_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_1641_, v_ref_1642_, v_msg_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
    crate::leanh::lean_dec(v___y_1651_);
    crate::leanh::lean_dec_ref(v___y_1650_);
    crate::leanh::lean_dec(v___y_1649_);
    crate::leanh::lean_dec_ref(v___y_1648_);
    crate::leanh::lean_dec(v___y_1647_);
    crate::leanh::lean_dec_ref(v___y_1646_);
    crate::leanh::lean_dec(v___y_1645_);
    crate::leanh::lean_dec_ref(v___y_1644_);
    crate::leanh::lean_dec(v_ref_1642_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(
    mut v_00_u03b1_1654_: *mut crate::leanh::LeanObject,
    mut v_msg_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1655_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v___x_1665_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(
    mut v_00_u03b1_1666_: *mut crate::leanh::LeanObject,
    mut v_msg_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
    crate::leanh::lean_dec(v___y_1675_);
    crate::leanh::lean_dec_ref(v___y_1674_);
    crate::leanh::lean_dec(v___y_1673_);
    crate::leanh::lean_dec_ref(v___y_1672_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v___y_1670_);
    crate::leanh::lean_dec(v___y_1669_);
    crate::leanh::lean_dec_ref(v___y_1668_);
    return v_res_1677_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0;
    v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1681_) == 0 {
                    v___x_1683_ = l_List_reverse___redArg(v_a_1682_);
                    return v___x_1683_;
                } else {
                    v_head_1684_ = crate::leanh::lean_ctor_get(v_a_1681_, 0);
                    v_tail_1685_ = crate::leanh::lean_ctor_get(v_a_1681_, 1);
                    v_isSharedCheck_1697_ = (!crate::leanh::lean_is_exclusive(v_a_1681_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1687_ = v_a_1681_;
                        v_isShared_1688_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1685_);
                        crate::leanh::lean_inc(v_head_1684_);
                        crate::leanh::lean_dec(v_a_1681_);
                        v___x_1687_ = crate::leanh::lean_box(0);
                        v_isShared_1688_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                v___x_1690_ = l_Lean_MessageData_ofSyntax(v_head_1684_);
                v___x_1691_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1689_);
                crate::leanh::lean_ctor_set(v___x_1691_, 1, v___x_1690_);
                v___x_1692_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                crate::leanh::lean_ctor_set(v___x_1692_, 1, v___x_1689_);
                if v_isShared_1688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1687_, 1, v_a_1682_);
                    crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1692_);
                    v___x_1694_ = v___x_1687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1682_);
                    v___x_1694_ = v_reuseFailAlloc_1696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1681_ = v_tail_1685_;
                v_a_1682_ = v___x_1694_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(
    mut v_msg_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1704_ = crate::leanh::lean_ctor_get(v___y_1701_, 5);
                v___x_1705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
                v_a_1706_ = crate::leanh::lean_ctor_get(v___x_1705_, 0);
                v_isSharedCheck_1714_ = (!crate::leanh::lean_is_exclusive(v___x_1705_)) as u8;
                if v_isSharedCheck_1714_ == 0 {
                    v___x_1708_ = v___x_1705_;
                    v_isShared_1709_ = v_isSharedCheck_1714_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1706_);
                    crate::leanh::lean_dec(v___x_1705_);
                    v___x_1708_ = crate::leanh::lean_box(0);
                    v_isShared_1709_ = v_isSharedCheck_1714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1704_);
                v___x_1710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1710_, 0, v_ref_1704_);
                crate::leanh::lean_ctor_set(v___x_1710_, 1, v_a_1706_);
                if v_isShared_1709_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1708_, 1);
                    crate::leanh::lean_ctor_set(v___x_1708_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(
    mut v_msg_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
    crate::leanh::lean_dec(v___y_1719_);
    crate::leanh::lean_dec_ref(v___y_1718_);
    crate::leanh::lean_dec(v___y_1717_);
    crate::leanh::lean_dec_ref(v___y_1716_);
    return v_res_1721_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(
    mut v_ref_1722_: *mut crate::leanh::LeanObject,
    mut v_msg_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1741_: u8 = 0;
    let mut v_cancelTk_x3f_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1743_: u8 = 0;
    let mut v_inheritedTraceOptions_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1729_ = crate::leanh::lean_ctor_get(v___y_1726_, 0);
    v_fileMap_1730_ = crate::leanh::lean_ctor_get(v___y_1726_, 1);
    v_options_1731_ = crate::leanh::lean_ctor_get(v___y_1726_, 2);
    v_currRecDepth_1732_ = crate::leanh::lean_ctor_get(v___y_1726_, 3);
    v_maxRecDepth_1733_ = crate::leanh::lean_ctor_get(v___y_1726_, 4);
    v_ref_1734_ = crate::leanh::lean_ctor_get(v___y_1726_, 5);
    v_currNamespace_1735_ = crate::leanh::lean_ctor_get(v___y_1726_, 6);
    v_openDecls_1736_ = crate::leanh::lean_ctor_get(v___y_1726_, 7);
    v_initHeartbeats_1737_ = crate::leanh::lean_ctor_get(v___y_1726_, 8);
    v_maxHeartbeats_1738_ = crate::leanh::lean_ctor_get(v___y_1726_, 9);
    v_quotContext_1739_ = crate::leanh::lean_ctor_get(v___y_1726_, 10);
    v_currMacroScope_1740_ = crate::leanh::lean_ctor_get(v___y_1726_, 11);
    v_diag_1741_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1726_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1742_ = crate::leanh::lean_ctor_get(v___y_1726_, 12);
    v_suppressElabErrors_1743_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1726_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1744_ = crate::leanh::lean_ctor_get(v___y_1726_, 13);
    v_ref_1745_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1734_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1744_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1742_);
    crate::leanh::lean_inc(v_currMacroScope_1740_);
    crate::leanh::lean_inc(v_quotContext_1739_);
    crate::leanh::lean_inc(v_maxHeartbeats_1738_);
    crate::leanh::lean_inc(v_initHeartbeats_1737_);
    crate::leanh::lean_inc(v_openDecls_1736_);
    crate::leanh::lean_inc(v_currNamespace_1735_);
    crate::leanh::lean_inc(v_maxRecDepth_1733_);
    crate::leanh::lean_inc(v_currRecDepth_1732_);
    crate::leanh::lean_inc_ref(v_options_1731_);
    crate::leanh::lean_inc_ref(v_fileMap_1730_);
    crate::leanh::lean_inc_ref(v_fileName_1729_);
    v___x_1746_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1746_, 0, v_fileName_1729_);
    crate::leanh::lean_ctor_set(v___x_1746_, 1, v_fileMap_1730_);
    crate::leanh::lean_ctor_set(v___x_1746_, 2, v_options_1731_);
    crate::leanh::lean_ctor_set(v___x_1746_, 3, v_currRecDepth_1732_);
    crate::leanh::lean_ctor_set(v___x_1746_, 4, v_maxRecDepth_1733_);
    crate::leanh::lean_ctor_set(v___x_1746_, 5, v_ref_1745_);
    crate::leanh::lean_ctor_set(v___x_1746_, 6, v_currNamespace_1735_);
    crate::leanh::lean_ctor_set(v___x_1746_, 7, v_openDecls_1736_);
    crate::leanh::lean_ctor_set(v___x_1746_, 8, v_initHeartbeats_1737_);
    crate::leanh::lean_ctor_set(v___x_1746_, 9, v_maxHeartbeats_1738_);
    crate::leanh::lean_ctor_set(v___x_1746_, 10, v_quotContext_1739_);
    crate::leanh::lean_ctor_set(v___x_1746_, 11, v_currMacroScope_1740_);
    crate::leanh::lean_ctor_set(v___x_1746_, 12, v_cancelTk_x3f_1742_);
    crate::leanh::lean_ctor_set(v___x_1746_, 13, v_inheritedTraceOptions_1744_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1746_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1741_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1746_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1743_,
    );
    v___x_1747_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1723_, v___y_1724_, v___y_1725_, v___x_1746_, v___y_1727_);
    crate::leanh::lean_dec_ref_known(v___x_1746_, 14);
    return v___x_1747_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(
    mut v_ref_1748_: *mut crate::leanh::LeanObject,
    mut v_msg_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_1748_, v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    crate::leanh::lean_dec(v___y_1753_);
    crate::leanh::lean_dec_ref(v___y_1752_);
    crate::leanh::lean_dec(v___y_1751_);
    crate::leanh::lean_dec_ref(v___y_1750_);
    crate::leanh::lean_dec(v_ref_1748_);
    return v_res_1755_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0;
    v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1760_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2;
    v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4;
    v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
    v___x_1766_ = l_Lean_MessageData_hint_x27(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(
    mut v_stx_1775_: *mut crate::leanh::LeanObject,
    mut v_simplifyTarget_1776_: u8,
    mut v_hyps_1777_: *mut crate::leanh::LeanObject,
    mut v_a_1778_: *mut crate::leanh::LeanObject,
    mut v_a_1779_: *mut crate::leanh::LeanObject,
    mut v_a_1780_: *mut crate::leanh::LeanObject,
    mut v_a_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hypsStr_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_simplifyTarget_1776_ == 0 {
                    v___x_1808_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11;
                    v___y_1802_ = v___x_1808_;
                    state = 2;
                    continue;
                } else {
                    v___x_1809_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12;
                    v___y_1802_ = v___x_1809_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1786_ = lean_array_to_list(v_hyps_1777_);
                v___x_1787_ = crate::leanh::lean_box(0);
                v___x_1788_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_1786_, v___x_1787_);
                v___x_1789_ = l_Lean_MessageData_andList(v___x_1788_);
                crate::leanh::lean_inc_ref(v___y_1785_);
                v_hypsStr_1790_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_hypsStr_1790_, 0, v___y_1785_);
                crate::leanh::lean_ctor_set(v_hypsStr_1790_, 1, v___x_1789_);
                v___x_1791_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
                crate::leanh::lean_inc_ref(v___y_1784_);
                v___x_1792_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1792_, 0, v___y_1784_);
                v___x_1793_ = l_Lean_MessageData_ofFormat(v___x_1792_);
                v___x_1794_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1794_, 0, v___x_1793_);
                crate::leanh::lean_ctor_set(v___x_1794_, 1, v_hypsStr_1790_);
                v___x_1795_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1791_);
                crate::leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                v___x_1796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
                v___x_1797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1797_, 0, v___x_1795_);
                crate::leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                v___x_1798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
                v___x_1799_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1799_, 0, v___x_1797_);
                crate::leanh::lean_ctor_set(v___x_1799_, 1, v___x_1798_);
                v___x_1800_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_1775_, v___x_1799_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
                return v___x_1800_;
            }
            2 => {
                v___x_1803_ = lean_array_get_size(v_hyps_1777_);
                v___x_1804_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1805_ = lean_nat_dec_eq(v___x_1803_, v___x_1804_);
                if v___x_1805_ == 0 {
                    v___x_1806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
                    v___y_1784_ = v___y_1802_;
                    v___y_1785_ = v___x_1806_;
                    state = 1;
                    continue;
                } else {
                    v___x_1807_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
                    v___y_1784_ = v___y_1802_;
                    v___y_1785_ = v___x_1807_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(
    mut v_stx_1810_: *mut crate::leanh::LeanObject,
    mut v_simplifyTarget_1811_: *mut crate::leanh::LeanObject,
    mut v_hyps_1812_: *mut crate::leanh::LeanObject,
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simplifyTarget_boxed_1818_: u8 = 0;
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_1818_ = (crate::leanh::lean_unbox(v_simplifyTarget_1811_) as u8);
    v_res_1819_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_1810_, v_simplifyTarget_boxed_1818_, v_hyps_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
    crate::leanh::lean_dec(v_a_1816_);
    crate::leanh::lean_dec_ref(v_a_1815_);
    crate::leanh::lean_dec(v_a_1814_);
    crate::leanh::lean_dec_ref(v_a_1813_);
    crate::leanh::lean_dec(v_stx_1810_);
    return v_res_1819_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(
    mut v_stx_1820_: *mut crate::leanh::LeanObject,
    mut v_simplifyTarget_1821_: u8,
    mut v_hyps_1822_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1823_: *mut crate::leanh::LeanObject,
    mut v_a_1824_: *mut crate::leanh::LeanObject,
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1829_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_1820_, v_simplifyTarget_1821_, v_hyps_1822_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
    return v___x_1829_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(
    mut v_stx_1830_: *mut crate::leanh::LeanObject,
    mut v_simplifyTarget_1831_: *mut crate::leanh::LeanObject,
    mut v_hyps_1832_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simplifyTarget_boxed_1839_: u8 = 0;
    let mut v_res_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_1839_ = (crate::leanh::lean_unbox(v_simplifyTarget_1831_) as u8);
    v_res_1840_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(
            v_stx_1830_,
            v_simplifyTarget_boxed_1839_,
            v_hyps_1832_,
            v_00_u03b1_1833_,
            v_a_1834_,
            v_a_1835_,
            v_a_1836_,
            v_a_1837_,
        );
    crate::leanh::lean_dec(v_a_1837_);
    crate::leanh::lean_dec_ref(v_a_1836_);
    crate::leanh::lean_dec(v_a_1835_);
    crate::leanh::lean_dec_ref(v_a_1834_);
    crate::leanh::lean_dec(v_stx_1830_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(
    mut v_00_u03b1_1841_: *mut crate::leanh::LeanObject,
    mut v_ref_1842_: *mut crate::leanh::LeanObject,
    mut v_msg_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_1842_, v_msg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(
    mut v_00_u03b1_1850_: *mut crate::leanh::LeanObject,
    mut v_ref_1851_: *mut crate::leanh::LeanObject,
    mut v_msg_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_1850_, v_ref_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
    crate::leanh::lean_dec(v___y_1856_);
    crate::leanh::lean_dec_ref(v___y_1855_);
    crate::leanh::lean_dec(v___y_1854_);
    crate::leanh::lean_dec_ref(v___y_1853_);
    crate::leanh::lean_dec(v_ref_1851_);
    return v_res_1858_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(
    mut v_00_u03b1_1859_: *mut crate::leanh::LeanObject,
    mut v_msg_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    return v___x_1866_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(
    mut v_00_u03b1_1867_: *mut crate::leanh::LeanObject,
    mut v_msg_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_1867_, v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    crate::leanh::lean_dec(v___y_1870_);
    crate::leanh::lean_dec_ref(v___y_1869_);
    return v_res_1874_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1876_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(
    mut v_type_1890_: *mut crate::leanh::LeanObject,
    mut v___x_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1907_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = l_Lean_Expr_getAppFn(v___x_1891_);
                if crate::leanh::lean_obj_tag(v___x_1917_) == 4 {
                    v_declName_1918_ = crate::leanh::lean_ctor_get(v___x_1917_, 0);
                    crate::leanh::lean_inc_n(v_declName_1918_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1917_, 2);
                    v___x_1919_ = lean_st_ref_get(v___y_1895_);
                    v_env_1920_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                    crate::leanh::lean_inc_ref_n(v_env_1920_, 2);
                    crate::leanh::lean_dec(v___x_1919_);
                    v___x_1921_ = l_Lean_isStructure(v_env_1920_, v_declName_1918_);
                    if v___x_1921_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1920_);
                        crate::leanh::lean_dec(v_declName_1918_);
                        v_a_1907_ = v___x_1921_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1922_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1923_ = l_Lean_getStructureFields(v_env_1920_, v_declName_1918_);
                        v___x_1924_ = lean_array_get_size(v___x_1923_);
                        crate::leanh::lean_dec_ref(v___x_1923_);
                        v___x_1925_ = lean_nat_dec_lt(v___x_1922_, v___x_1924_);
                        v_a_1907_ = v___x_1925_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1917_);
                    v___x_1926_ = 0;
                    v_a_1907_ = v___x_1926_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
                crate::leanh::lean_inc_ref(v_val_1898_);
                v___x_1900_ = l_Lean_stringToMessageData(v_val_1898_);
                v___x_1901_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1901_, 1, v___x_1900_);
                v___x_1902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
                v___x_1903_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1901_);
                crate::leanh::lean_ctor_set(v___x_1903_, 1, v___x_1902_);
                v___x_1904_ = l_Lean_MessageData_hint_x27(v___x_1903_);
                v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                return v___x_1905_;
            }
            2 => {
                v___x_1908_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5;
                v___x_1909_ = l_Lean_Expr_isAppOf(v_type_1890_, v___x_1908_);
                if v___x_1909_ == 0 {
                    v___x_1910_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7;
                    v___x_1911_ = l_Lean_Expr_isAppOf(v_type_1890_, v___x_1910_);
                    if v___x_1911_ == 0 {
                        if v_a_1907_ == 0 {
                            v___x_1912_ = l_Lean_MessageData_nil;
                            v___x_1913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1913_, 0, v___x_1912_);
                            return v___x_1913_;
                        } else {
                            v___x_1914_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8;
                            v_val_1898_ = v___x_1914_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1915_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9;
                        v_val_1898_ = v___x_1915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1916_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10;
                    v_val_1898_ = v___x_1916_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(
    mut v_type_1927_: *mut crate::leanh::LeanObject,
    mut v___x_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
    mut v___y_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(
            v_type_1927_,
            v___x_1928_,
            v___y_1929_,
            v___y_1930_,
            v___y_1931_,
            v___y_1932_,
        );
    crate::leanh::lean_dec(v___y_1932_);
    crate::leanh::lean_dec_ref(v___y_1931_);
    crate::leanh::lean_dec(v___y_1930_);
    crate::leanh::lean_dec_ref(v___y_1929_);
    crate::leanh::lean_dec_ref(v___x_1928_);
    crate::leanh::lean_dec_ref(v_type_1927_);
    return v_res_1934_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(
    mut v_type_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lean_Expr_getAppFn(v_type_1935_);
    v___f_1937_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
    crate::leanh::lean_closure_set(v___f_1937_, 0, v_type_1935_);
    crate::leanh::lean_closure_set(v___f_1937_, 1, v___x_1936_);
    v___x_1938_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5;
    v___x_1939_ = l_Lean_MessageData_ofLazyM(v___f_1937_, v___x_1938_);
    return v___x_1939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1;
    v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(
    mut v_mvarId_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1945_);
                v___x_1951_ = l_Lean_MVarId_getType(
                    v_mvarId_1945_,
                    v_a_1946_,
                    v_a_1947_,
                    v_a_1948_,
                    v_a_1949_,
                );
                if crate::leanh::lean_obj_tag(v___x_1951_) == 0 {
                    v_a_1952_ = crate::leanh::lean_ctor_get(v___x_1951_, 0);
                    crate::leanh::lean_inc(v_a_1952_);
                    crate::leanh::lean_dec_ref_known(v___x_1951_, 1);
                    v___x_1953_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_1952_);
                    v___x_1954_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
                    v___x_1955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
                    v___x_1956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1955_);
                    crate::leanh::lean_ctor_set(v___x_1956_, 1, v___x_1953_);
                    v___x_1957_ =
                        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
                    v___x_1958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1956_);
                    crate::leanh::lean_ctor_set(v___x_1958_, 1, v___x_1957_);
                    v___x_1959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1959_, 0, v___x_1958_);
                    v___x_1960_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_1954_,
                        v_mvarId_1945_,
                        v___x_1959_,
                        v_a_1946_,
                        v_a_1947_,
                        v_a_1948_,
                        v_a_1949_,
                    );
                    return v___x_1960_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1945_);
                    v_a_1961_ = crate::leanh::lean_ctor_get(v___x_1951_, 0);
                    v_isSharedCheck_1968_ = (!crate::leanh::lean_is_exclusive(v___x_1951_)) as u8;
                    if v_isSharedCheck_1968_ == 0 {
                        v___x_1963_ = v___x_1951_;
                        v_isShared_1964_ = v_isSharedCheck_1968_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1961_);
                        crate::leanh::lean_dec(v___x_1951_);
                        v___x_1963_ = crate::leanh::lean_box(0);
                        v_isShared_1964_ = v_isSharedCheck_1968_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1964_ == 0 {
                    v___x_1966_ = v___x_1963_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
                    v___x_1966_ = v_reuseFailAlloc_1967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___boxed(
    mut v_mvarId_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
    mut v_a_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(
            v_mvarId_1969_,
            v_a_1970_,
            v_a_1971_,
            v_a_1972_,
            v_a_1973_,
        );
    crate::leanh::lean_dec(v_a_1973_);
    crate::leanh::lean_dec_ref(v_a_1972_);
    crate::leanh::lean_dec(v_a_1971_);
    crate::leanh::lean_dec_ref(v_a_1970_);
    return v_res_1975_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0;
    v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1980_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2;
    v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
    return v___x_1981_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(
    mut v_fvarId_1982_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
    mut v_a_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_1982_);
                v___x_1989_ =
                    l_Lean_FVarId_getType___redArg(v_fvarId_1982_, v_a_1984_, v_a_1986_, v_a_1987_);
                if crate::leanh::lean_obj_tag(v___x_1989_) == 0 {
                    v_a_1990_ = crate::leanh::lean_ctor_get(v___x_1989_, 0);
                    crate::leanh::lean_inc_n(v_a_1990_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1989_, 1);
                    v___x_1991_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
                    v___x_1992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1);
                    v___x_1993_ = crate::leanh::lean_unsigned_to_nat(30);
                    v___x_1994_ = l_Lean_inlineExpr(v_a_1990_, v___x_1993_);
                    v___x_1995_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_1992_);
                    crate::leanh::lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    v___x_1996_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3);
                    v___x_1997_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_1995_);
                    crate::leanh::lean_ctor_set(v___x_1997_, 1, v___x_1996_);
                    v___x_1998_ = l_Lean_Expr_fvar___override(v_fvarId_1982_);
                    v___x_1999_ = l_Lean_MessageData_ofExpr(v___x_1998_);
                    v___x_2000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2000_, 0, v___x_1997_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 1, v___x_1999_);
                    v___x_2001_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                    v___x_2002_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2002_, 0, v___x_2000_);
                    crate::leanh::lean_ctor_set(v___x_2002_, 1, v___x_2001_);
                    v___x_2003_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_1990_);
                    v___x_2004_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2004_, 0, v___x_2002_);
                    crate::leanh::lean_ctor_set(v___x_2004_, 1, v___x_2003_);
                    v___x_2005_ =
                        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
                    v___x_2006_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2006_, 0, v___x_2004_);
                    crate::leanh::lean_ctor_set(v___x_2006_, 1, v___x_2005_);
                    v___x_2007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2007_, 0, v___x_2006_);
                    v___x_2008_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_1991_,
                        v_mvarId_1983_,
                        v___x_2007_,
                        v_a_1984_,
                        v_a_1985_,
                        v_a_1986_,
                        v_a_1987_,
                    );
                    return v___x_2008_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1983_);
                    crate::leanh::lean_dec(v_fvarId_1982_);
                    v_a_2009_ = crate::leanh::lean_ctor_get(v___x_1989_, 0);
                    v_isSharedCheck_2016_ = (!crate::leanh::lean_is_exclusive(v___x_1989_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2011_ = v___x_1989_;
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2009_);
                        crate::leanh::lean_dec(v___x_1989_);
                        v___x_2011_ = crate::leanh::lean_box(0);
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2012_ == 0 {
                    v___x_2014_ = v___x_2011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
                    v___x_2014_ = v_reuseFailAlloc_2015_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(
    mut v_fvarId_2017_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2018_: *mut crate::leanh::LeanObject,
    mut v_a_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2024_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(
            v_fvarId_2017_,
            v_mvarId_2018_,
            v_a_2019_,
            v_a_2020_,
            v_a_2021_,
            v_a_2022_,
        );
    crate::leanh::lean_dec(v_a_2022_);
    crate::leanh::lean_dec_ref(v_a_2021_);
    crate::leanh::lean_dec(v_a_2020_);
    crate::leanh::lean_dec_ref(v_a_2019_);
    return v_res_2024_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2025_) == 0 {
                    v___x_2027_ = l_List_reverse___redArg(v_a_2026_);
                    return v___x_2027_;
                } else {
                    v_head_2028_ = crate::leanh::lean_ctor_get(v_a_2025_, 0);
                    v_tail_2029_ = crate::leanh::lean_ctor_get(v_a_2025_, 1);
                    v_isSharedCheck_2042_ = (!crate::leanh::lean_is_exclusive(v_a_2025_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v___x_2031_ = v_a_2025_;
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2029_);
                        crate::leanh::lean_inc(v_head_2028_);
                        crate::leanh::lean_dec(v_a_2025_);
                        v___x_2031_ = crate::leanh::lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2033_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                v___x_2034_ = l_Lean_Expr_fvar___override(v_head_2028_);
                v___x_2035_ = l_Lean_MessageData_ofExpr(v___x_2034_);
                v___x_2036_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2036_, 0, v___x_2033_);
                crate::leanh::lean_ctor_set(v___x_2036_, 1, v___x_2035_);
                v___x_2037_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2036_);
                crate::leanh::lean_ctor_set(v___x_2037_, 1, v___x_2033_);
                if v_isShared_2032_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2031_, 1, v_a_2026_);
                    crate::leanh::lean_ctor_set(v___x_2031_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2026_);
                    v___x_2039_ = v_reuseFailAlloc_2041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2025_ = v_tail_2029_;
                v_a_2026_ = v___x_2039_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1;
    v___x_2047_ = l_Lean_MessageData_ofFormat(v___x_2046_);
    return v___x_2047_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_note_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
    v_note_2049_ = l_Lean_MessageData_note(v___x_2048_);
    return v_note_2049_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4;
    v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v_note_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_note_2053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
    v___x_2054_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
    v___x_2055_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2054_);
    crate::leanh::lean_ctor_set(v___x_2055_, 1, v_note_2053_);
    return v___x_2055_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
    v___x_2057_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
    v___x_2058_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    crate::leanh::lean_ctor_set(v___x_2058_, 1, v___x_2056_);
    return v___x_2058_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
    v___x_2060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    return v___x_2060_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10;
    v___x_2065_ = l_Lean_MessageData_ofFormat(v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12;
    v___x_2068_ = l_Lean_stringToMessageData(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(
    mut v_fvarIds_2069_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
    mut v_a_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_note_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    v_note_2076_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
    v___x_2077_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2078_ = lean_array_get_size(v_fvarIds_2069_);
    v___x_2079_ = lean_nat_dec_lt(v___x_2077_, v___x_2078_);
    if v___x_2079_ == 0 {
        let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_fvarIds_2069_);
        v___x_2080_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
        v___x_2081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
        v___x_2082_ = l_Lean_Meta_throwTacticEx___redArg(
            v___x_2080_,
            v_mvarId_2070_,
            v___x_2081_,
            v_a_2071_,
            v_a_2072_,
            v_a_2073_,
            v_a_2074_,
        );
        return v___x_2082_;
    } else {
        let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fvarMsgs_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fvarMsgs_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2083_ = lean_array_to_list(v_fvarIds_2069_);
        v___x_2084_ = crate::leanh::lean_box(0);
        v_fvarMsgs_2085_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_2083_, v___x_2084_);
        v___x_2086_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
        v_fvarMsgs_2087_ = l_Lean_MessageData_joinSep(v_fvarMsgs_2085_, v___x_2086_);
        v___x_2088_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
        v___x_2089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
        v___x_2090_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2090_, 0, v___x_2089_);
        crate::leanh::lean_ctor_set(v___x_2090_, 1, v_fvarMsgs_2087_);
        v___x_2091_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2091_, 0, v___x_2090_);
        crate::leanh::lean_ctor_set(v___x_2091_, 1, v_note_2076_);
        v___x_2092_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
        v___x_2093_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2093_, 0, v___x_2091_);
        crate::leanh::lean_ctor_set(v___x_2093_, 1, v___x_2092_);
        v___x_2094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2093_);
        v___x_2095_ = l_Lean_Meta_throwTacticEx___redArg(
            v___x_2088_,
            v_mvarId_2070_,
            v___x_2094_,
            v_a_2071_,
            v_a_2072_,
            v_a_2073_,
            v_a_2074_,
        );
        return v___x_2095_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(
    mut v_fvarIds_2096_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2103_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_2096_, v_mvarId_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
    crate::leanh::lean_dec(v_a_2101_);
    crate::leanh::lean_dec_ref(v_a_2100_);
    crate::leanh::lean_dec(v_a_2099_);
    crate::leanh::lean_dec_ref(v_a_2098_);
    return v_res_2103_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(
    mut v_00_u03b1_2104_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_2105_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_2105_, v_mvarId_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
    return v___x_2112_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(
    mut v_00_u03b1_2113_: *mut crate::leanh::LeanObject,
    mut v_fvarIds_2114_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2115_: *mut crate::leanh::LeanObject,
    mut v_a_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(
            v_00_u03b1_2113_,
            v_fvarIds_2114_,
            v_mvarId_2115_,
            v_a_2116_,
            v_a_2117_,
            v_a_2118_,
            v_a_2119_,
        );
    crate::leanh::lean_dec(v_a_2119_);
    crate::leanh::lean_dec_ref(v_a_2118_);
    crate::leanh::lean_dec(v_a_2117_);
    crate::leanh::lean_dec_ref(v_a_2116_);
    return v_res_2121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(
    mut v_a_2125_: *mut crate::leanh::LeanObject,
    mut v_as_2126_: *mut crate::leanh::LeanObject,
    mut v_sz_2127_: usize,
    mut v_i_2128_: usize,
    mut v_b_2129_: *mut crate::leanh::LeanObject,
    mut v___y_2130_: *mut crate::leanh::LeanObject,
    mut v___y_2131_: *mut crate::leanh::LeanObject,
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: usize = 0;
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2135_ = lean_usize_dec_lt(v_i_2128_, v_sz_2127_);
                if v___x_2135_ == 0 {
                    crate::leanh::lean_dec(v_a_2125_);
                    v___x_2136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2136_, 0, v_b_2129_);
                    return v___x_2136_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2129_);
                    v_a_2137_ = lean_array_uget_borrowed(v_as_2126_, v_i_2128_);
                    crate::leanh::lean_inc(v_a_2137_);
                    crate::leanh::lean_inc(v_a_2125_);
                    v___x_2138_ = l_Lean_Meta_splitLocalDecl_x3f(
                        v_a_2125_,
                        v_a_2137_,
                        v___y_2130_,
                        v___y_2131_,
                        v___y_2132_,
                        v___y_2133_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2138_) == 0 {
                        v_a_2139_ = crate::leanh::lean_ctor_get(v___x_2138_, 0);
                        v_isSharedCheck_2152_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2138_)) as u8;
                        if v_isSharedCheck_2152_ == 0 {
                            v___x_2141_ = v___x_2138_;
                            v_isShared_2142_ = v_isSharedCheck_2152_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2139_);
                            crate::leanh::lean_dec(v___x_2138_);
                            v___x_2141_ = crate::leanh::lean_box(0);
                            v_isShared_2142_ = v_isSharedCheck_2152_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2125_);
                        v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2138_, 0);
                        v_isSharedCheck_2160_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2138_)) as u8;
                        if v_isSharedCheck_2160_ == 0 {
                            v___x_2155_ = v___x_2138_;
                            v_isShared_2156_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2153_);
                            crate::leanh::lean_dec(v___x_2138_);
                            v___x_2155_ = crate::leanh::lean_box(0);
                            v_isShared_2156_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2143_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_a_2139_) == 1 {
                    crate::leanh::lean_dec(v_a_2125_);
                    v___x_2144_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2144_, 0, v_a_2139_);
                    crate::leanh::lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                    if v_isShared_2142_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2144_);
                        v___x_2146_ = v___x_2141_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
                        v___x_2146_ = v_reuseFailAlloc_2147_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2141_);
                    crate::leanh::lean_dec(v_a_2139_);
                    v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0;
                    v___x_2149_ = 1usize;
                    v___x_2150_ = lean_usize_add(v_i_2128_, v___x_2149_);
                    v_i_2128_ = v___x_2150_;
                    v_b_2129_ = v___x_2148_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_2146_;
            }
            3 => {
                if v_isShared_2156_ == 0 {
                    v___x_2158_ = v___x_2155_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
                    v___x_2158_ = v_reuseFailAlloc_2159_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(
    mut v_a_2161_: *mut crate::leanh::LeanObject,
    mut v_as_2162_: *mut crate::leanh::LeanObject,
    mut v_sz_2163_: *mut crate::leanh::LeanObject,
    mut v_i_2164_: *mut crate::leanh::LeanObject,
    mut v_b_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
    mut v___y_2167_: *mut crate::leanh::LeanObject,
    mut v___y_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2171_: usize = 0;
    let mut v_i_boxed_2172_: usize = 0;
    let mut v_res_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2171_ = crate::leanh::lean_unbox_usize(v_sz_2163_);
    crate::leanh::lean_dec(v_sz_2163_);
    v_i_boxed_2172_ = crate::leanh::lean_unbox_usize(v_i_2164_);
    crate::leanh::lean_dec(v_i_2164_);
    v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_2161_, v_as_2162_, v_sz_boxed_2171_, v_i_boxed_2172_, v_b_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
    crate::leanh::lean_dec(v___y_2169_);
    crate::leanh::lean_dec_ref(v___y_2168_);
    crate::leanh::lean_dec(v___y_2167_);
    crate::leanh::lean_dec_ref(v___y_2166_);
    crate::leanh::lean_dec_ref(v_as_2162_);
    return v_res_2173_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__0(
    mut v___y_2174_: *mut crate::leanh::LeanObject,
    mut v___y_2175_: *mut crate::leanh::LeanObject,
    mut v___y_2176_: *mut crate::leanh::LeanObject,
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v___y_2178_: *mut crate::leanh::LeanObject,
    mut v___y_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_unused_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2200_: usize = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_a_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_val_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_a_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2195_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_2175_,
                    v___y_2178_,
                    v___y_2179_,
                    v___y_2180_,
                    v___y_2181_,
                );
                if crate::leanh::lean_obj_tag(v___x_2195_) == 0 {
                    v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                    crate::leanh::lean_inc_n(v_a_2196_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2195_, 1);
                    v___x_2197_ = l_Lean_MVarId_getNondepPropHyps(
                        v_a_2196_,
                        v___y_2178_,
                        v___y_2179_,
                        v___y_2180_,
                        v___y_2181_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2197_) == 0 {
                        v_a_2198_ = crate::leanh::lean_ctor_get(v___x_2197_, 0);
                        crate::leanh::lean_inc(v_a_2198_);
                        crate::leanh::lean_dec_ref_known(v___x_2197_, 1);
                        v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0;
                        v_sz_2200_ = lean_array_size(v_a_2198_);
                        v___x_2201_ = 0usize;
                        crate::leanh::lean_inc(v_a_2196_);
                        v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_2196_, v_a_2198_, v_sz_2200_, v___x_2201_, v___x_2199_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
                        if crate::leanh::lean_obj_tag(v___x_2202_) == 0 {
                            v_a_2203_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
                            crate::leanh::lean_inc(v_a_2203_);
                            crate::leanh::lean_dec_ref_known(v___x_2202_, 1);
                            v_fst_2204_ = crate::leanh::lean_ctor_get(v_a_2203_, 0);
                            crate::leanh::lean_inc(v_fst_2204_);
                            crate::leanh::lean_dec(v_a_2203_);
                            if crate::leanh::lean_obj_tag(v_fst_2204_) == 0 {
                                v___x_2205_ = 1;
                                v___x_2206_ = 0;
                                crate::leanh::lean_inc(v_a_2196_);
                                v___x_2207_ = l_Lean_Meta_splitTarget_x3f(
                                    v_a_2196_,
                                    v___x_2205_,
                                    v___x_2206_,
                                    v___y_2178_,
                                    v___y_2179_,
                                    v___y_2180_,
                                    v___y_2181_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2207_) == 0 {
                                    v_a_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                                    crate::leanh::lean_inc(v_a_2208_);
                                    crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2208_) == 1 {
                                        crate::leanh::lean_dec(v_a_2198_);
                                        crate::leanh::lean_dec(v_a_2196_);
                                        v_val_2209_ = crate::leanh::lean_ctor_get(v_a_2208_, 0);
                                        crate::leanh::lean_inc(v_val_2209_);
                                        crate::leanh::lean_dec_ref_known(v_a_2208_, 1);
                                        v_a_2184_ = v_val_2209_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2208_);
                                        v___x_2210_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_2198_, v_a_2196_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
                                        if crate::leanh::lean_obj_tag(v___x_2210_) == 0 {
                                            v_a_2211_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                                            crate::leanh::lean_inc(v_a_2211_);
                                            crate::leanh::lean_dec_ref_known(v___x_2210_, 1);
                                            v_a_2184_ = v_a_2211_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_2212_ = crate::leanh::lean_ctor_get(v___x_2210_, 0);
                                            v_isSharedCheck_2219_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2210_))
                                                    as u8;
                                            if v_isSharedCheck_2219_ == 0 {
                                                v___x_2214_ = v___x_2210_;
                                                v_isShared_2215_ = v_isSharedCheck_2219_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2212_);
                                                crate::leanh::lean_dec(v___x_2210_);
                                                v___x_2214_ = crate::leanh::lean_box(0);
                                                v_isShared_2215_ = v_isSharedCheck_2219_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2198_);
                                    crate::leanh::lean_dec(v_a_2196_);
                                    v_a_2220_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                                    v_isSharedCheck_2227_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2207_)) as u8;
                                    if v_isSharedCheck_2227_ == 0 {
                                        v___x_2222_ = v___x_2207_;
                                        v_isShared_2223_ = v_isSharedCheck_2227_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2220_);
                                        crate::leanh::lean_dec(v___x_2207_);
                                        v___x_2222_ = crate::leanh::lean_box(0);
                                        v_isShared_2223_ = v_isSharedCheck_2227_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2198_);
                                crate::leanh::lean_dec(v_a_2196_);
                                v_val_2228_ = crate::leanh::lean_ctor_get(v_fst_2204_, 0);
                                crate::leanh::lean_inc(v_val_2228_);
                                crate::leanh::lean_dec_ref_known(v_fst_2204_, 1);
                                v_a_2184_ = v_val_2228_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2198_);
                            crate::leanh::lean_dec(v_a_2196_);
                            v_a_2229_ = crate::leanh::lean_ctor_get(v___x_2202_, 0);
                            v_isSharedCheck_2236_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2202_)) as u8;
                            if v_isSharedCheck_2236_ == 0 {
                                v___x_2231_ = v___x_2202_;
                                v_isShared_2232_ = v_isSharedCheck_2236_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2229_);
                                crate::leanh::lean_dec(v___x_2202_);
                                v___x_2231_ = crate::leanh::lean_box(0);
                                v_isShared_2232_ = v_isSharedCheck_2236_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2196_);
                        v_a_2237_ = crate::leanh::lean_ctor_get(v___x_2197_, 0);
                        v_isSharedCheck_2244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2197_)) as u8;
                        if v_isSharedCheck_2244_ == 0 {
                            v___x_2239_ = v___x_2197_;
                            v_isShared_2240_ = v_isSharedCheck_2244_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2237_);
                            crate::leanh::lean_dec(v___x_2197_);
                            v___x_2239_ = crate::leanh::lean_box(0);
                            v_isShared_2240_ = v_isSharedCheck_2244_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_a_2245_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                    v_isSharedCheck_2252_ = (!crate::leanh::lean_is_exclusive(v___x_2195_)) as u8;
                    if v_isSharedCheck_2252_ == 0 {
                        v___x_2247_ = v___x_2195_;
                        v_isShared_2248_ = v_isSharedCheck_2252_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2245_);
                        crate::leanh::lean_dec(v___x_2195_);
                        v___x_2247_ = crate::leanh::lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2252_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2185_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_2184_,
                    v___y_2175_,
                    v___y_2178_,
                    v___y_2179_,
                    v___y_2180_,
                    v___y_2181_,
                );
                if crate::leanh::lean_obj_tag(v___x_2185_) == 0 {
                    v_isSharedCheck_2193_ = (!crate::leanh::lean_is_exclusive(v___x_2185_)) as u8;
                    if v_isSharedCheck_2193_ == 0 {
                        v_unused_2194_ = crate::leanh::lean_ctor_get(v___x_2185_, 0);
                        crate::leanh::lean_dec(v_unused_2194_);
                        v___x_2187_ = v___x_2185_;
                        v_isShared_2188_ = v_isSharedCheck_2193_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2185_);
                        v___x_2187_ = crate::leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2193_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2185_;
                }
            }
            2 => {
                v___x_2189_ = crate::leanh::lean_box(0);
                if v_isShared_2188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2189_);
                    v___x_2191_ = v___x_2187_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
                    v___x_2191_ = v_reuseFailAlloc_2192_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2191_;
            }
            4 => {
                if v_isShared_2215_ == 0 {
                    v___x_2217_ = v___x_2214_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
                    v___x_2217_ = v_reuseFailAlloc_2218_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2217_;
            }
            6 => {
                if v_isShared_2223_ == 0 {
                    v___x_2225_ = v___x_2222_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
                    v___x_2225_ = v_reuseFailAlloc_2226_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2225_;
            }
            8 => {
                if v_isShared_2232_ == 0 {
                    v___x_2234_ = v___x_2231_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2235_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2234_;
            }
            10 => {
                if v_isShared_2240_ == 0 {
                    v___x_2242_ = v___x_2239_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
                    v___x_2242_ = v_reuseFailAlloc_2243_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2242_;
            }
            12 => {
                if v_isShared_2248_ == 0 {
                    v___x_2250_ = v___x_2247_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Lean_Elab_Tactic_evalSplit___lam__0(
        v___y_2253_,
        v___y_2254_,
        v___y_2255_,
        v___y_2256_,
        v___y_2257_,
        v___y_2258_,
        v___y_2259_,
        v___y_2260_,
    );
    crate::leanh::lean_dec(v___y_2260_);
    crate::leanh::lean_dec_ref(v___y_2259_);
    crate::leanh::lean_dec(v___y_2258_);
    crate::leanh::lean_dec_ref(v___y_2257_);
    crate::leanh::lean_dec(v___y_2256_);
    crate::leanh::lean_dec_ref(v___y_2255_);
    crate::leanh::lean_dec(v___y_2254_);
    crate::leanh::lean_dec_ref(v___y_2253_);
    return v_res_2262_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__1(
    mut v_type_2263_: u8,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v_unused_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2300_: u8 = 0;
    let mut v_a_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2304_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut v_a_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2312_: u8 = 0;
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2285_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_2265_,
                    v___y_2268_,
                    v___y_2269_,
                    v___y_2270_,
                    v___y_2271_,
                );
                if crate::leanh::lean_obj_tag(v___x_2285_) == 0 {
                    v_a_2286_ = crate::leanh::lean_ctor_get(v___x_2285_, 0);
                    crate::leanh::lean_inc_n(v_a_2286_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2285_, 1);
                    v___x_2287_ = 0;
                    v___x_2288_ = l_Lean_Meta_splitTarget_x3f(
                        v_a_2286_,
                        v_type_2263_,
                        v___x_2287_,
                        v___y_2268_,
                        v___y_2269_,
                        v___y_2270_,
                        v___y_2271_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2288_) == 0 {
                        v_a_2289_ = crate::leanh::lean_ctor_get(v___x_2288_, 0);
                        crate::leanh::lean_inc(v_a_2289_);
                        crate::leanh::lean_dec_ref_known(v___x_2288_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2289_) == 1 {
                            crate::leanh::lean_dec(v_a_2286_);
                            v_val_2290_ = crate::leanh::lean_ctor_get(v_a_2289_, 0);
                            crate::leanh::lean_inc(v_val_2290_);
                            crate::leanh::lean_dec_ref_known(v_a_2289_, 1);
                            v_a_2274_ = v_val_2290_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2289_);
                            v___x_2291_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_2286_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
                            if crate::leanh::lean_obj_tag(v___x_2291_) == 0 {
                                v_a_2292_ = crate::leanh::lean_ctor_get(v___x_2291_, 0);
                                crate::leanh::lean_inc(v_a_2292_);
                                crate::leanh::lean_dec_ref_known(v___x_2291_, 1);
                                v_a_2274_ = v_a_2292_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2293_ = crate::leanh::lean_ctor_get(v___x_2291_, 0);
                                v_isSharedCheck_2300_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2291_)) as u8;
                                if v_isSharedCheck_2300_ == 0 {
                                    v___x_2295_ = v___x_2291_;
                                    v_isShared_2296_ = v_isSharedCheck_2300_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2293_);
                                    crate::leanh::lean_dec(v___x_2291_);
                                    v___x_2295_ = crate::leanh::lean_box(0);
                                    v_isShared_2296_ = v_isSharedCheck_2300_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2286_);
                        v_a_2301_ = crate::leanh::lean_ctor_get(v___x_2288_, 0);
                        v_isSharedCheck_2308_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2288_)) as u8;
                        if v_isSharedCheck_2308_ == 0 {
                            v___x_2303_ = v___x_2288_;
                            v_isShared_2304_ = v_isSharedCheck_2308_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2301_);
                            crate::leanh::lean_dec(v___x_2288_);
                            v___x_2303_ = crate::leanh::lean_box(0);
                            v_isShared_2304_ = v_isSharedCheck_2308_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_2309_ = crate::leanh::lean_ctor_get(v___x_2285_, 0);
                    v_isSharedCheck_2316_ = (!crate::leanh::lean_is_exclusive(v___x_2285_)) as u8;
                    if v_isSharedCheck_2316_ == 0 {
                        v___x_2311_ = v___x_2285_;
                        v_isShared_2312_ = v_isSharedCheck_2316_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2309_);
                        crate::leanh::lean_dec(v___x_2285_);
                        v___x_2311_ = crate::leanh::lean_box(0);
                        v_isShared_2312_ = v_isSharedCheck_2316_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2275_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_2274_,
                    v___y_2265_,
                    v___y_2268_,
                    v___y_2269_,
                    v___y_2270_,
                    v___y_2271_,
                );
                if crate::leanh::lean_obj_tag(v___x_2275_) == 0 {
                    v_isSharedCheck_2283_ = (!crate::leanh::lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2283_ == 0 {
                        v_unused_2284_ = crate::leanh::lean_ctor_get(v___x_2275_, 0);
                        crate::leanh::lean_dec(v_unused_2284_);
                        v___x_2277_ = v___x_2275_;
                        v_isShared_2278_ = v_isSharedCheck_2283_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2275_);
                        v___x_2277_ = crate::leanh::lean_box(0);
                        v_isShared_2278_ = v_isSharedCheck_2283_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2275_;
                }
            }
            2 => {
                v___x_2279_ = crate::leanh::lean_box(0);
                if v_isShared_2278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2279_);
                    v___x_2281_ = v___x_2277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2281_;
            }
            4 => {
                if v_isShared_2296_ == 0 {
                    v___x_2298_ = v___x_2295_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
                    v___x_2298_ = v_reuseFailAlloc_2299_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2298_;
            }
            6 => {
                if v_isShared_2304_ == 0 {
                    v___x_2306_ = v___x_2303_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2306_;
            }
            8 => {
                if v_isShared_2312_ == 0 {
                    v___x_2314_ = v___x_2311_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
                    v___x_2314_ = v_reuseFailAlloc_2315_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(
    mut v_type_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_4513__boxed_2327_: u8 = 0;
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_4513__boxed_2327_ = (crate::leanh::lean_unbox(v_type_2317_) as u8);
    v_res_2328_ = l_Lean_Elab_Tactic_evalSplit___lam__1(
        v_type_4513__boxed_2327_,
        v___y_2318_,
        v___y_2319_,
        v___y_2320_,
        v___y_2321_,
        v___y_2322_,
        v___y_2323_,
        v___y_2324_,
        v___y_2325_,
    );
    crate::leanh::lean_dec(v___y_2325_);
    crate::leanh::lean_dec_ref(v___y_2324_);
    crate::leanh::lean_dec(v___y_2323_);
    crate::leanh::lean_dec_ref(v___y_2322_);
    crate::leanh::lean_dec(v___y_2321_);
    crate::leanh::lean_dec_ref(v___y_2320_);
    crate::leanh::lean_dec(v___y_2319_);
    crate::leanh::lean_dec_ref(v___y_2318_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__2(
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_unused_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_a_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_a_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2351_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_2331_,
                    v___y_2334_,
                    v___y_2335_,
                    v___y_2336_,
                    v___y_2337_,
                );
                if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    crate::leanh::lean_inc_n(v_a_2352_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2351_, 1);
                    crate::leanh::lean_inc(v_a_2329_);
                    v___x_2353_ = l_Lean_Meta_splitLocalDecl_x3f(
                        v_a_2352_,
                        v_a_2329_,
                        v___y_2334_,
                        v___y_2335_,
                        v___y_2336_,
                        v___y_2337_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2353_) == 0 {
                        v_a_2354_ = crate::leanh::lean_ctor_get(v___x_2353_, 0);
                        crate::leanh::lean_inc(v_a_2354_);
                        crate::leanh::lean_dec_ref_known(v___x_2353_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2354_) == 1 {
                            crate::leanh::lean_dec(v_a_2352_);
                            crate::leanh::lean_dec(v_a_2329_);
                            v_val_2355_ = crate::leanh::lean_ctor_get(v_a_2354_, 0);
                            crate::leanh::lean_inc(v_val_2355_);
                            crate::leanh::lean_dec_ref_known(v_a_2354_, 1);
                            v_a_2340_ = v_val_2355_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2354_);
                            v___x_2356_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_2329_, v_a_2352_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
                            if crate::leanh::lean_obj_tag(v___x_2356_) == 0 {
                                v_a_2357_ = crate::leanh::lean_ctor_get(v___x_2356_, 0);
                                crate::leanh::lean_inc(v_a_2357_);
                                crate::leanh::lean_dec_ref_known(v___x_2356_, 1);
                                v_a_2340_ = v_a_2357_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2358_ = crate::leanh::lean_ctor_get(v___x_2356_, 0);
                                v_isSharedCheck_2365_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2356_)) as u8;
                                if v_isSharedCheck_2365_ == 0 {
                                    v___x_2360_ = v___x_2356_;
                                    v_isShared_2361_ = v_isSharedCheck_2365_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2358_);
                                    crate::leanh::lean_dec(v___x_2356_);
                                    v___x_2360_ = crate::leanh::lean_box(0);
                                    v_isShared_2361_ = v_isSharedCheck_2365_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2352_);
                        crate::leanh::lean_dec(v_a_2329_);
                        v_a_2366_ = crate::leanh::lean_ctor_get(v___x_2353_, 0);
                        v_isSharedCheck_2373_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2353_)) as u8;
                        if v_isSharedCheck_2373_ == 0 {
                            v___x_2368_ = v___x_2353_;
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2366_);
                            crate::leanh::lean_dec(v___x_2353_);
                            v___x_2368_ = crate::leanh::lean_box(0);
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2329_);
                    v_a_2374_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2381_ = (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2376_ = v___x_2351_;
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2374_);
                        crate::leanh::lean_dec(v___x_2351_);
                        v___x_2376_ = crate::leanh::lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2341_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_2340_,
                    v___y_2331_,
                    v___y_2334_,
                    v___y_2335_,
                    v___y_2336_,
                    v___y_2337_,
                );
                if crate::leanh::lean_obj_tag(v___x_2341_) == 0 {
                    v_isSharedCheck_2349_ = (!crate::leanh::lean_is_exclusive(v___x_2341_)) as u8;
                    if v_isSharedCheck_2349_ == 0 {
                        v_unused_2350_ = crate::leanh::lean_ctor_get(v___x_2341_, 0);
                        crate::leanh::lean_dec(v_unused_2350_);
                        v___x_2343_ = v___x_2341_;
                        v_isShared_2344_ = v_isSharedCheck_2349_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2341_);
                        v___x_2343_ = crate::leanh::lean_box(0);
                        v_isShared_2344_ = v_isSharedCheck_2349_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2341_;
                }
            }
            2 => {
                v___x_2345_ = crate::leanh::lean_box(0);
                if v_isShared_2344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2343_, 0, v___x_2345_);
                    v___x_2347_ = v___x_2343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
                    v___x_2347_ = v_reuseFailAlloc_2348_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2347_;
            }
            4 => {
                if v_isShared_2361_ == 0 {
                    v___x_2363_ = v___x_2360_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
                    v___x_2363_ = v_reuseFailAlloc_2364_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2363_;
            }
            6 => {
                if v_isShared_2369_ == 0 {
                    v___x_2371_ = v___x_2368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2372_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2371_;
            }
            8 => {
                if v_isShared_2377_ == 0 {
                    v___x_2379_ = v___x_2376_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2392_ = l_Lean_Elab_Tactic_evalSplit___lam__2(
        v_a_2382_,
        v___y_2383_,
        v___y_2384_,
        v___y_2385_,
        v___y_2386_,
        v___y_2387_,
        v___y_2388_,
        v___y_2389_,
        v___y_2390_,
    );
    crate::leanh::lean_dec(v___y_2390_);
    crate::leanh::lean_dec_ref(v___y_2389_);
    crate::leanh::lean_dec(v___y_2388_);
    crate::leanh::lean_dec_ref(v___y_2387_);
    crate::leanh::lean_dec(v___y_2386_);
    crate::leanh::lean_dec_ref(v___y_2385_);
    crate::leanh::lean_dec(v___y_2384_);
    crate::leanh::lean_dec_ref(v___y_2383_);
    return v_res_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit(
    mut v_stx_2394_: *mut crate::leanh::LeanObject,
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_a_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: u8 = 0;
    let mut v___y_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: u8 = 0;
    let mut v___y_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: u8 = 0;
    let mut v___y_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2459_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___f_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hypotheses_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u8 = 0;
    let mut v_loc_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2463_ = l_Lean_Elab_Tactic_evalSplit___closed__0;
                v___x_2484_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
                crate::leanh::lean_inc(v_stx_2394_);
                v___x_2485_ = l_Lean_Syntax_isOfKind(v_stx_2394_, v___x_2484_);
                if v___x_2485_ == 0 {
                    v___y_2465_ = v_a_2395_;
                    v___y_2466_ = v_a_2396_;
                    v___y_2467_ = v_a_2397_;
                    v___y_2468_ = v_a_2398_;
                    v___y_2469_ = v_a_2399_;
                    v___y_2470_ = v_a_2400_;
                    v___y_2471_ = v_a_2401_;
                    v___y_2472_ = v_a_2402_;
                    state = 6;
                    continue;
                } else {
                    v___x_2486_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2487_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2486_);
                    crate::leanh::lean_inc(v___x_2487_);
                    v___x_2488_ = l_Lean_Syntax_matchesNull(v___x_2487_, v___x_2486_);
                    if v___x_2488_ == 0 {
                        crate::leanh::lean_dec(v___x_2487_);
                        v___y_2465_ = v_a_2395_;
                        v___y_2466_ = v_a_2396_;
                        v___y_2467_ = v_a_2397_;
                        v___y_2468_ = v_a_2398_;
                        v___y_2469_ = v_a_2399_;
                        v___y_2470_ = v_a_2400_;
                        v___y_2471_ = v_a_2401_;
                        v___y_2472_ = v_a_2402_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2489_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_t_2490_ = l_Lean_Syntax_getArg(v___x_2487_, v___x_2489_);
                        crate::leanh::lean_dec(v___x_2487_);
                        v___x_2502_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2503_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2502_);
                        v___x_2504_ = l_Lean_Syntax_isNone(v___x_2503_);
                        if v___x_2504_ == 0 {
                            crate::leanh::lean_inc(v___x_2503_);
                            v___x_2505_ = l_Lean_Syntax_matchesNull(v___x_2503_, v___x_2486_);
                            if v___x_2505_ == 0 {
                                crate::leanh::lean_dec(v___x_2503_);
                                crate::leanh::lean_dec(v_t_2490_);
                                v___y_2465_ = v_a_2395_;
                                v___y_2466_ = v_a_2396_;
                                v___y_2467_ = v_a_2397_;
                                v___y_2468_ = v_a_2398_;
                                v___y_2469_ = v_a_2399_;
                                v___y_2470_ = v_a_2400_;
                                v___y_2471_ = v_a_2401_;
                                v___y_2472_ = v_a_2402_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2506_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2489_);
                                crate::leanh::lean_dec(v___x_2503_);
                                v___x_2507_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10;
                                crate::leanh::lean_inc(v___x_2506_);
                                v___x_2508_ = l_Lean_Syntax_isOfKind(v___x_2506_, v___x_2507_);
                                if v___x_2508_ == 0 {
                                    crate::leanh::lean_dec(v___x_2506_);
                                    crate::leanh::lean_dec(v_t_2490_);
                                    v___y_2465_ = v_a_2395_;
                                    v___y_2466_ = v_a_2396_;
                                    v___y_2467_ = v_a_2397_;
                                    v___y_2468_ = v_a_2398_;
                                    v___y_2469_ = v_a_2399_;
                                    v___y_2470_ = v_a_2400_;
                                    v___y_2471_ = v_a_2401_;
                                    v___y_2472_ = v_a_2402_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_loc_2509_ = l_Lean_Syntax_getArg(v___x_2506_, v___x_2486_);
                                    crate::leanh::lean_dec(v___x_2506_);
                                    v___x_2510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2510_, 0, v_loc_2509_);
                                    v___y_2492_ = v_a_2398_;
                                    v___y_2493_ = v_a_2395_;
                                    v___y_2494_ = v_a_2399_;
                                    v___y_2495_ = v_a_2397_;
                                    v___y_2496_ = v_a_2396_;
                                    v___y_2497_ = v_a_2402_;
                                    v___y_2498_ = v_a_2401_;
                                    v___y_2499_ = v_a_2400_;
                                    v___y_2500_ = v___x_2510_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2503_);
                            v___x_2511_ = crate::leanh::lean_box(0);
                            v___y_2492_ = v_a_2398_;
                            v___y_2493_ = v_a_2395_;
                            v___y_2494_ = v_a_2399_;
                            v___y_2495_ = v_a_2397_;
                            v___y_2496_ = v_a_2396_;
                            v___y_2497_ = v_a_2402_;
                            v___y_2498_ = v_a_2401_;
                            v___y_2499_ = v_a_2400_;
                            v___y_2500_ = v___x_2511_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2406_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_2405_);
                    v___x_2416_ = crate::leanh::lean_box(0);
                    v___x_2417_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2418_ = lean_array_get(v___x_2416_, v___y_2407_, v___x_2417_);
                    crate::leanh::lean_dec_ref(v___y_2407_);
                    v___x_2419_ = l_Lean_Elab_Tactic_getFVarId(
                        v___x_2418_,
                        v___y_2408_,
                        v___y_2409_,
                        v___y_2410_,
                        v___y_2411_,
                        v___y_2412_,
                        v___y_2413_,
                        v___y_2414_,
                        v___y_2415_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2419_) == 0 {
                        v_a_2420_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
                        crate::leanh::lean_inc(v_a_2420_);
                        crate::leanh::lean_dec_ref_known(v___x_2419_, 1);
                        v___f_2421_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_evalSplit___lam__2___boxed as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_2421_, 0, v_a_2420_);
                        v___x_2422_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                            v___f_2421_,
                            v___y_2408_,
                            v___y_2409_,
                            v___y_2410_,
                            v___y_2411_,
                            v___y_2412_,
                            v___y_2413_,
                            v___y_2414_,
                            v___y_2415_,
                        );
                        return v___x_2422_;
                    } else {
                        v_a_2423_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
                        v_isSharedCheck_2430_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2419_)) as u8;
                        if v_isSharedCheck_2430_ == 0 {
                            v___x_2425_ = v___x_2419_;
                            v_isShared_2426_ = v_isSharedCheck_2430_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2423_);
                            crate::leanh::lean_dec(v___x_2419_);
                            v___x_2425_ = crate::leanh::lean_box(0);
                            v_isShared_2426_ = v_isSharedCheck_2430_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2407_);
                    v___x_2431_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___y_2405_,
                        v___y_2408_,
                        v___y_2409_,
                        v___y_2410_,
                        v___y_2411_,
                        v___y_2412_,
                        v___y_2413_,
                        v___y_2414_,
                        v___y_2415_,
                    );
                    return v___x_2431_;
                }
            }
            2 => {
                if v_isShared_2426_ == 0 {
                    v___x_2428_ = v___x_2425_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
                    v___x_2428_ = v_reuseFailAlloc_2429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2428_;
            }
            4 => {
                crate::leanh::lean_dec_ref(v___y_2433_);
                v___x_2445_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_2442_, v___y_2440_, v___y_2444_, v___y_2439_, v___y_2441_, v___y_2437_, v___y_2443_);
                crate::leanh::lean_dec(v___y_2442_);
                return v___x_2445_;
            }
            5 => {
                if v___y_2459_ == 0 {
                    v___x_2460_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2461_ = lean_array_get_size(v___y_2449_);
                    v___x_2462_ = lean_nat_dec_lt(v___x_2460_, v___x_2461_);
                    if v___x_2462_ == 0 {
                        crate::leanh::lean_dec(v___y_2457_);
                        v___y_2405_ = v___y_2447_;
                        v___y_2406_ = v___y_2448_;
                        v___y_2407_ = v___y_2449_;
                        v___y_2408_ = v___y_2454_;
                        v___y_2409_ = v___y_2452_;
                        v___y_2410_ = v___y_2451_;
                        v___y_2411_ = v___y_2450_;
                        v___y_2412_ = v___y_2455_;
                        v___y_2413_ = v___y_2456_;
                        v___y_2414_ = v___y_2453_;
                        v___y_2415_ = v___y_2458_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2433_ = v___y_2447_;
                        v___y_2434_ = v___y_2450_;
                        v___y_2435_ = v___y_2451_;
                        v___y_2436_ = v___y_2452_;
                        v___y_2437_ = v___y_2453_;
                        v___y_2438_ = v___y_2454_;
                        v___y_2439_ = v___y_2455_;
                        v___y_2440_ = v___y_2448_;
                        v___y_2441_ = v___y_2456_;
                        v___y_2442_ = v___y_2457_;
                        v___y_2443_ = v___y_2458_;
                        v___y_2444_ = v___y_2449_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_2433_ = v___y_2447_;
                    v___y_2434_ = v___y_2450_;
                    v___y_2435_ = v___y_2451_;
                    v___y_2436_ = v___y_2452_;
                    v___y_2437_ = v___y_2453_;
                    v___y_2438_ = v___y_2454_;
                    v___y_2439_ = v___y_2455_;
                    v___y_2440_ = v___y_2448_;
                    v___y_2441_ = v___y_2456_;
                    v___y_2442_ = v___y_2457_;
                    v___y_2443_ = v___y_2458_;
                    v___y_2444_ = v___y_2449_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2473_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2474_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2473_);
                crate::leanh::lean_dec(v_stx_2394_);
                v_loc_2475_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2474_);
                if crate::leanh::lean_obj_tag(v_loc_2475_) == 0 {
                    crate::leanh::lean_dec(v___x_2474_);
                    v___x_2476_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_2463_,
                        v___y_2465_,
                        v___y_2466_,
                        v___y_2467_,
                        v___y_2468_,
                        v___y_2469_,
                        v___y_2470_,
                        v___y_2471_,
                        v___y_2472_,
                    );
                    return v___x_2476_;
                } else {
                    v_hypotheses_2477_ = crate::leanh::lean_ctor_get(v_loc_2475_, 0);
                    crate::leanh::lean_inc_ref(v_hypotheses_2477_);
                    v_type_2478_ = crate::leanh::lean_ctor_get_uint8(
                        v_loc_2475_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_loc_2475_, 1);
                    v___x_2479_ = crate::leanh::lean_box((v_type_2478_) as usize);
                    v___f_2480_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalSplit___lam__1___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2480_, 0, v___x_2479_);
                    v___x_2481_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2482_ = lean_array_get_size(v_hypotheses_2477_);
                    v___x_2483_ = lean_nat_dec_lt(v___x_2481_, v___x_2482_);
                    if v___x_2483_ == 0 {
                        v___y_2447_ = v___f_2480_;
                        v___y_2448_ = v_type_2478_;
                        v___y_2449_ = v_hypotheses_2477_;
                        v___y_2450_ = v___y_2468_;
                        v___y_2451_ = v___y_2467_;
                        v___y_2452_ = v___y_2466_;
                        v___y_2453_ = v___y_2471_;
                        v___y_2454_ = v___y_2465_;
                        v___y_2455_ = v___y_2469_;
                        v___y_2456_ = v___y_2470_;
                        v___y_2457_ = v___x_2474_;
                        v___y_2458_ = v___y_2472_;
                        v___y_2459_ = v___x_2483_;
                        state = 5;
                        continue;
                    } else {
                        v___y_2447_ = v___f_2480_;
                        v___y_2448_ = v_type_2478_;
                        v___y_2449_ = v_hypotheses_2477_;
                        v___y_2450_ = v___y_2468_;
                        v___y_2451_ = v___y_2467_;
                        v___y_2452_ = v___y_2466_;
                        v___y_2453_ = v___y_2471_;
                        v___y_2454_ = v___y_2465_;
                        v___y_2455_ = v___y_2469_;
                        v___y_2456_ = v___y_2470_;
                        v___y_2457_ = v___x_2474_;
                        v___y_2458_ = v___y_2472_;
                        v___y_2459_ = v_type_2478_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2501_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_2490_, v___y_2500_, v___y_2493_, v___y_2496_, v___y_2495_, v___y_2492_, v___y_2494_, v___y_2499_, v___y_2498_, v___y_2497_);
                if crate::leanh::lean_obj_tag(v___x_2501_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2501_, 1);
                    v___y_2465_ = v___y_2493_;
                    v___y_2466_ = v___y_2496_;
                    v___y_2467_ = v___y_2495_;
                    v___y_2468_ = v___y_2492_;
                    v___y_2469_ = v___y_2494_;
                    v___y_2470_ = v___y_2499_;
                    v___y_2471_ = v___y_2498_;
                    v___y_2472_ = v___y_2497_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_stx_2394_);
                    return v___x_2501_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___boxed(
    mut v_stx_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_a_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2522_ = l_Lean_Elab_Tactic_evalSplit(
        v_stx_2512_,
        v_a_2513_,
        v_a_2514_,
        v_a_2515_,
        v_a_2516_,
        v_a_2517_,
        v_a_2518_,
        v_a_2519_,
        v_a_2520_,
    );
    crate::leanh::lean_dec(v_a_2520_);
    crate::leanh::lean_dec_ref(v_a_2519_);
    crate::leanh::lean_dec(v_a_2518_);
    crate::leanh::lean_dec_ref(v_a_2517_);
    crate::leanh::lean_dec(v_a_2516_);
    crate::leanh::lean_dec_ref(v_a_2515_);
    crate::leanh::lean_dec(v_a_2514_);
    crate::leanh::lean_dec_ref(v_a_2513_);
    return v_res_2522_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2532_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
    v___x_2533_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2;
    v___x_2534_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalSplit___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2535_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2531_,
        v___x_2532_,
        v___x_2533_,
        v___x_2534_,
    );
    return v___x_2535_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(
    mut v_a_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2537_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
    return v_res_2537_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2;
    v___x_2565_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6;
    v___x_2566_ = l_Lean_addBuiltinDeclarationRanges(v___x_2564_, v___x_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(
    mut v_a_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
    return v_res_2568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Split(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint =
        _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint,
    );
    res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Split(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Split(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Split(builtin);
}
