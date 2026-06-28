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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value: LeanStringObject<87> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [85, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 116, 114, 97, 99, 101, 46, 115, 112, 108, 105, 116, 46, 102, 97, 105, 108, 117, 114, 101, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 100, 105, 115, 112, 108, 97, 121, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 97, 105, 108, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut LeanObject,13219768312984610626 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value) as *mut LeanObject,8171071557273278778 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value) as *mut LeanObject,16145843736367156323 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut LeanObject,1731991885970815592 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value) as *mut LeanObject,1767494567867404924 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [108, 111, 99, 97, 116, 105, 111, 110, 72, 121, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value) as *mut LeanObject,12722427251967365861 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [84, 111, 32, 97, 112, 112, 108, 121, 32, 96, 115, 112, 108, 105, 116, 96, 32, 97, 116, 32, 116, 104, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [96, 44, 32, 117, 115, 101, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 115, 112, 108, 105, 116, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 83, 112, 101, 99, 105, 102, 121, 105, 110, 103, 32, 97, 32, 116, 101, 114, 109, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 121, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value) as *mut LeanObject;
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [84, 97, 99, 116, 105, 99, 32, 96, 115, 112, 108, 105, 116, 96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 83, 112, 101, 99, 105, 102, 121, 105, 110, 103, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [41, 32, 105, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value: LeanStringObject<112> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 112, m_capacity: 112, m_length: 111, m_data: [83, 112, 101, 99, 105, 102, 121, 32, 97, 32, 115, 105, 110, 103, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 116, 111, 32, 115, 112, 108, 105, 116, 44, 32, 111, 114, 32, 117, 115, 101, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 42, 96, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 116, 97, 114, 103, 101, 116, 32, 116, 104, 97, 116, 32, 99, 97, 110, 32, 98, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 104, 101, 32, 103, 111, 97, 108, 32, 97, 110, 100, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [73, 102, 32, 121, 111, 117, 32, 109, 101, 97, 110, 116, 32, 116, 111, 32, 100, 101, 115, 116, 114, 117, 99, 116, 32, 116, 104, 105, 115, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [44, 32, 117, 115, 101, 32, 116, 104, 101, 32, 96, 99, 97, 115, 101, 115, 96, 32, 116, 97, 99, 116, 105, 99, 32, 105, 110, 115, 116, 101, 97, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value) as *mut LeanObject,9743492140944907313 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value) as *mut LeanObject,15289851429949568889 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 97, 105, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 106, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value) as *mut LeanObject,18188493160499796729 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 97, 110, 32, 96, 105, 102, 96, 32, 111, 114, 32, 96, 109, 97, 116, 99, 104, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value: LeanStringObject<58> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 58, m_capacity: 58, m_length: 57, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 97, 110, 32, 96, 105, 102, 96, 32, 111, 114, 32, 96, 109, 97, 116, 99, 104, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 102, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value: LeanStringObject<187> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 187, m_capacity: 187, m_length: 186, m_data: [96, 115, 112, 108, 105, 116, 32, 97, 116, 32, 42, 96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 97, 116, 116, 101, 109, 112, 116, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 97, 116, 32, 110, 111, 110, 45, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 111, 114, 32, 116, 104, 111, 115, 101, 32, 111, 110, 32, 119, 104, 105, 99, 104, 32, 111, 116, 104, 101, 114, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 100, 101, 112, 101, 110, 100, 46, 32, 73, 116, 32, 109, 97, 121, 32, 115, 116, 105, 108, 108, 32, 98, 101, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 109, 97, 110, 117, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 32, 97, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 117, 115, 105, 110, 103, 32, 96, 115, 112, 108, 105, 116, 32, 97, 116, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value: LeanStringObject<89> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 103, 111, 97, 108, 44, 32, 97, 110, 100, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 116, 104, 97, 116, 32, 99, 111, 117, 108, 100, 32, 98, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 112, 108, 105, 116, 32, 119, 101, 114, 101, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 111, 114, 32, 97, 110, 121, 32, 111, 102, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalSplit___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_evalSplit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalSplit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalSplit___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 83, 112, 108, 105, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value) as *mut LeanObject,6451815636812638566 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(
    mut v_k_1285_: *mut LeanObject,
    mut v_defValue_1286_: u8,
    mut v___y_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1297_: u8 = 0;
    let mut v_v_1298_: u8 = 0;
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1289_ = lean_ctor_get(v___y_1287_, 2);
                v_map_1290_ = lean_ctor_get(v_options_1289_, 0);
                v___x_1291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1290_, v_k_1285_);
                if lean_obj_tag(v___x_1291_) == 0 {
                    v___x_1292_ = lean_box((v_defValue_1286_) as usize);
                    v___x_1293_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1293_, 0, v___x_1292_);
                    return v___x_1293_;
                } else {
                    v_val_1294_ = lean_ctor_get(v___x_1291_, 0);
                    v_isSharedCheck_1307_ = (!lean_is_exclusive(v___x_1291_)) as u8;
                    if v_isSharedCheck_1307_ == 0 {
                        v___x_1296_ = v___x_1291_;
                        v_isShared_1297_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1294_);
                        lean_dec(v___x_1291_);
                        v___x_1296_ = lean_box(0);
                        v_isShared_1297_ = v_isSharedCheck_1307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_val_1294_) == 1 {
                    v_v_1298_ = lean_ctor_get_uint8(v_val_1294_, 0 as u32);
                    lean_dec_ref_known(v_val_1294_, 0);
                    v___x_1299_ = lean_box((v_v_1298_) as usize);
                    if v_isShared_1297_ == 0 {
                        lean_ctor_set_tag(v___x_1296_, 0);
                        lean_ctor_set(v___x_1296_, 0, v___x_1299_);
                        v___x_1301_ = v___x_1296_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
                        v___x_1301_ = v_reuseFailAlloc_1302_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_val_1294_);
                    v___x_1303_ = lean_box((v_defValue_1286_) as usize);
                    if v_isShared_1297_ == 0 {
                        lean_ctor_set_tag(v___x_1296_, 0);
                        lean_ctor_set(v___x_1296_, 0, v___x_1303_);
                        v___x_1305_ = v___x_1296_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
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
    mut v_k_1308_: *mut LeanObject,
    mut v_defValue_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_1312_: u8 = 0;
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_1312_ = (lean_unbox(v_defValue_1309_) as u8);
    v_res_1313_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_1308_, v_defValue_boxed_1312_, v___y_1310_);
    lean_dec_ref(v___y_1310_);
    lean_dec(v_k_1308_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(
    mut v_k_1314_: *mut LeanObject,
    mut v_defValue_1315_: u8,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v___x_1321_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_1314_, v_defValue_1315_, v___y_1318_);
    return v___x_1321_;
}
pub unsafe fn l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___boxed(
    mut v_k_1322_: *mut LeanObject,
    mut v_defValue_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_1329_: u8 = 0;
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_1329_ = (lean_unbox(v_defValue_1323_) as u8);
    v_res_1330_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(v_k_1322_, v_defValue_boxed_1329_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
    lean_dec(v___y_1327_);
    lean_dec_ref(v___y_1326_);
    lean_dec(v___y_1325_);
    lean_dec_ref(v___y_1324_);
    lean_dec(v_k_1322_);
    return v_res_1330_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0;
    v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v___x_1334_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1);
    v___x_1335_ = l_Lean_MessageData_hint_x27(v___x_1334_);
    return v___x_1335_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(
    mut v___x_1336_: *mut LeanObject,
    mut v___x_1337_: u8,
    mut v___y_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
    mut v___y_1341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1343_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v___x_1336_, v___x_1337_, v___y_1340_);
                v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
                v_isSharedCheck_1357_ = (!lean_is_exclusive(v___x_1343_)) as u8;
                if v_isSharedCheck_1357_ == 0 {
                    v___x_1346_ = v___x_1343_;
                    v_isShared_1347_ = v_isSharedCheck_1357_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1344_);
                    lean_dec(v___x_1343_);
                    v___x_1346_ = lean_box(0);
                    v_isShared_1347_ = v_isSharedCheck_1357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1348_ = (lean_unbox(v_a_1344_) as u8);
                lean_dec(v_a_1344_);
                if v___x_1348_ == 0 {
                    v___x_1349_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2);
                    if v_isShared_1347_ == 0 {
                        lean_ctor_set(v___x_1346_, 0, v___x_1349_);
                        v___x_1351_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
                        v___x_1351_ = v_reuseFailAlloc_1352_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1353_ = l_Lean_MessageData_nil;
                    if v_isShared_1347_ == 0 {
                        lean_ctor_set(v___x_1346_, 0, v___x_1353_);
                        v___x_1355_ = v___x_1346_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
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
    mut v___x_1358_: *mut LeanObject,
    mut v___x_1359_: *mut LeanObject,
    mut v___y_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
    mut v___y_1362_: *mut LeanObject,
    mut v___y_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689__boxed_1365_: u8 = 0;
    let mut v_res_1366_: *mut LeanObject = core::ptr::null_mut();
    v___x_689__boxed_1365_ = (lean_unbox(v___x_1359_) as u8);
    v_res_1366_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(
            v___x_1358_,
            v___x_689__boxed_1365_,
            v___y_1360_,
            v___y_1361_,
            v___y_1362_,
            v___y_1363_,
        );
    lean_dec(v___y_1363_);
    lean_dec_ref(v___y_1362_);
    lean_dec(v___y_1361_);
    lean_dec_ref(v___y_1360_);
    lean_dec(v___x_1358_);
    return v_res_1366_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6()
-> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5;
    v___f_1381_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4;
    v___x_1382_ = l_Lean_MessageData_ofLazyM(v___f_1381_, v___x_1380_);
    return v___x_1382_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint()
-> *mut LeanObject {
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1383_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6);
    return v___x_1383_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(
    mut v_msgData_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v___y_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_st_ref_get(v___y_1388_);
    v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
    lean_inc_ref(v_env_1391_);
    lean_dec(v___x_1390_);
    v___x_1392_ = lean_st_ref_get(v___y_1386_);
    v_mctx_1393_ = lean_ctor_get(v___x_1392_, 0);
    lean_inc_ref(v_mctx_1393_);
    lean_dec(v___x_1392_);
    v_lctx_1394_ = lean_ctor_get(v___y_1385_, 2);
    v_options_1395_ = lean_ctor_get(v___y_1387_, 2);
    lean_inc_ref(v_options_1395_);
    lean_inc_ref(v_lctx_1394_);
    v___x_1396_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1396_, 0, v_env_1391_);
    lean_ctor_set(v___x_1396_, 1, v_mctx_1393_);
    lean_ctor_set(v___x_1396_, 2, v_lctx_1394_);
    lean_ctor_set(v___x_1396_, 3, v_options_1395_);
    v___x_1397_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1397_, 0, v___x_1396_);
    lean_ctor_set(v___x_1397_, 1, v_msgData_1384_);
    v___x_1398_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1398_, 0, v___x_1397_);
    return v___x_1398_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1405_: *mut LeanObject = core::ptr::null_mut();
    v_res_1405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
    lean_dec(v___y_1403_);
    lean_dec_ref(v___y_1402_);
    lean_dec(v___y_1401_);
    lean_dec_ref(v___y_1400_);
    return v_res_1405_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(
    mut v_msg_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1412_ = lean_ctor_get(v___y_1409_, 5);
                v___x_1413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
                v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
                v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1413_)) as u8;
                if v_isSharedCheck_1422_ == 0 {
                    v___x_1416_ = v___x_1413_;
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1414_);
                    lean_dec(v___x_1413_);
                    v___x_1416_ = lean_box(0);
                    v_isShared_1417_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1412_);
                v___x_1418_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1418_, 0, v_ref_1412_);
                lean_ctor_set(v___x_1418_, 1, v_a_1414_);
                if v_isShared_1417_ == 0 {
                    lean_ctor_set_tag(v___x_1416_, 1);
                    lean_ctor_set(v___x_1416_, 0, v___x_1418_);
                    v___x_1420_ = v___x_1416_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
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
    mut v_msg_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
    mut v___y_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
    lean_dec(v___y_1427_);
    lean_dec_ref(v___y_1426_);
    lean_dec(v___y_1425_);
    lean_dec_ref(v___y_1424_);
    return v_res_1429_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(
    mut v_ref_1430_: *mut LeanObject,
    mut v_msg_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
    mut v___y_1436_: *mut LeanObject,
    mut v___y_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1453_: u8 = 0;
    let mut v_cancelTk_x3f_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1455_: u8 = 0;
    let mut v_inheritedTraceOptions_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1441_ = lean_ctor_get(v___y_1438_, 0);
    v_fileMap_1442_ = lean_ctor_get(v___y_1438_, 1);
    v_options_1443_ = lean_ctor_get(v___y_1438_, 2);
    v_currRecDepth_1444_ = lean_ctor_get(v___y_1438_, 3);
    v_maxRecDepth_1445_ = lean_ctor_get(v___y_1438_, 4);
    v_ref_1446_ = lean_ctor_get(v___y_1438_, 5);
    v_currNamespace_1447_ = lean_ctor_get(v___y_1438_, 6);
    v_openDecls_1448_ = lean_ctor_get(v___y_1438_, 7);
    v_initHeartbeats_1449_ = lean_ctor_get(v___y_1438_, 8);
    v_maxHeartbeats_1450_ = lean_ctor_get(v___y_1438_, 9);
    v_quotContext_1451_ = lean_ctor_get(v___y_1438_, 10);
    v_currMacroScope_1452_ = lean_ctor_get(v___y_1438_, 11);
    v_diag_1453_ = lean_ctor_get_uint8(
        v___y_1438_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1454_ = lean_ctor_get(v___y_1438_, 12);
    v_suppressElabErrors_1455_ = lean_ctor_get_uint8(
        v___y_1438_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1456_ = lean_ctor_get(v___y_1438_, 13);
    v_ref_1457_ = l_Lean_replaceRef(v_ref_1430_, v_ref_1446_);
    lean_inc_ref(v_inheritedTraceOptions_1456_);
    lean_inc(v_cancelTk_x3f_1454_);
    lean_inc(v_currMacroScope_1452_);
    lean_inc(v_quotContext_1451_);
    lean_inc(v_maxHeartbeats_1450_);
    lean_inc(v_initHeartbeats_1449_);
    lean_inc(v_openDecls_1448_);
    lean_inc(v_currNamespace_1447_);
    lean_inc(v_maxRecDepth_1445_);
    lean_inc(v_currRecDepth_1444_);
    lean_inc_ref(v_options_1443_);
    lean_inc_ref(v_fileMap_1442_);
    lean_inc_ref(v_fileName_1441_);
    v___x_1458_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1458_, 0, v_fileName_1441_);
    lean_ctor_set(v___x_1458_, 1, v_fileMap_1442_);
    lean_ctor_set(v___x_1458_, 2, v_options_1443_);
    lean_ctor_set(v___x_1458_, 3, v_currRecDepth_1444_);
    lean_ctor_set(v___x_1458_, 4, v_maxRecDepth_1445_);
    lean_ctor_set(v___x_1458_, 5, v_ref_1457_);
    lean_ctor_set(v___x_1458_, 6, v_currNamespace_1447_);
    lean_ctor_set(v___x_1458_, 7, v_openDecls_1448_);
    lean_ctor_set(v___x_1458_, 8, v_initHeartbeats_1449_);
    lean_ctor_set(v___x_1458_, 9, v_maxHeartbeats_1450_);
    lean_ctor_set(v___x_1458_, 10, v_quotContext_1451_);
    lean_ctor_set(v___x_1458_, 11, v_currMacroScope_1452_);
    lean_ctor_set(v___x_1458_, 12, v_cancelTk_x3f_1454_);
    lean_ctor_set(v___x_1458_, 13, v_inheritedTraceOptions_1456_);
    lean_ctor_set_uint8(
        v___x_1458_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1453_,
    );
    lean_ctor_set_uint8(
        v___x_1458_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1455_,
    );
    v___x_1459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1431_, v___y_1436_, v___y_1437_, v___x_1458_, v___y_1439_);
    lean_dec_ref_known(v___x_1458_, 14);
    return v___x_1459_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(
    mut v_ref_1460_: *mut LeanObject,
    mut v_msg_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1471_: *mut LeanObject = core::ptr::null_mut();
    v_res_1471_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_1460_, v_msg_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
    lean_dec(v___y_1469_);
    lean_dec_ref(v___y_1468_);
    lean_dec(v___y_1467_);
    lean_dec_ref(v___y_1466_);
    lean_dec(v___y_1465_);
    lean_dec_ref(v___y_1464_);
    lean_dec(v___y_1463_);
    lean_dec_ref(v___y_1462_);
    lean_dec(v_ref_1460_);
    return v_res_1471_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    v___x_1486_ = l_Array_mkArray0(lean_box(0));
    return v___x_1486_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1501_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14;
    v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
    return v___x_1502_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    v___x_1504_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16;
    v___x_1505_ = l_Lean_stringToMessageData(v___x_1504_);
    return v___x_1505_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    v___x_1507_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18;
    v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
    return v___x_1508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(
    mut v___x_1509_: u8,
    mut v_t_1510_: *mut LeanObject,
    mut v_error_1511_: *mut LeanObject,
    mut v_loc_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
    mut v___y_1516_: *mut LeanObject,
    mut v___y_1517_: *mut LeanObject,
    mut v___y_1518_: *mut LeanObject,
    mut v___y_1519_: *mut LeanObject,
    mut v___y_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1526_: u8 = 0;
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1509_ == 0 {
                    v___x_1522_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                    return v___x_1522_;
                } else {
                    v_lctx_1523_ = lean_ctor_get(v___y_1517_, 2);
                    v_name_1524_ = l_Lean_Syntax_getId(v_t_1510_);
                    v___x_1580_ = l_Lean_Name_isStr(v_name_1524_);
                    if v___x_1580_ == 0 {
                        v___y_1526_ = v___x_1580_;
                        state = 1;
                        continue;
                    } else {
                        if lean_obj_tag(v_loc_1512_) == 0 {
                            v___y_1526_ = v___x_1580_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_name_1524_);
                            v___x_1581_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                            return v___x_1581_;
                        }
                    }
                }
            }
            1 => {
                if v___y_1526_ == 0 {
                    lean_dec(v_name_1524_);
                    v___x_1527_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v_error_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                    return v___x_1527_;
                } else {
                    v___x_1528_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1523_, v_name_1524_);
                    if lean_obj_tag(v___x_1528_) == 1 {
                        v_val_1529_ = lean_ctor_get(v___x_1528_, 0);
                        lean_inc(v_val_1529_);
                        lean_dec_ref_known(v___x_1528_, 1);
                        v_ref_1530_ = lean_ctor_get(v___y_1519_, 5);
                        v___x_1531_ = l_Lean_LocalDecl_toExpr(v_val_1529_);
                        v___x_1532_ = 0;
                        v___x_1533_ = l_Lean_SourceInfo_fromRef(v_ref_1530_, v___x_1532_);
                        v___x_1534_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1;
                        v___x_1535_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1;
                        v___x_1536_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
                        lean_inc_n(v___x_1533_, 7);
                        v___x_1537_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1537_, 0, v___x_1533_);
                        lean_ctor_set(v___x_1537_, 1, v___x_1535_);
                        v___x_1538_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7;
                        v___x_1539_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
                        v___x_1540_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_1540_, 0, v___x_1533_);
                        lean_ctor_set(v___x_1540_, 1, v___x_1538_);
                        lean_ctor_set(v___x_1540_, 2, v___x_1539_);
                        v___x_1541_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10;
                        v___x_1542_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11;
                        v___x_1543_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v___x_1543_, 0, v___x_1533_);
                        lean_ctor_set(v___x_1543_, 1, v___x_1542_);
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
                        v___x_1551_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
                        v___x_1552_ = l_Lean_MessageData_ofExpr(v___x_1531_);
                        lean_inc_ref(v___x_1552_);
                        v___x_1553_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1553_, 0, v___x_1551_);
                        lean_ctor_set(v___x_1553_, 1, v___x_1552_);
                        v___x_1554_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
                        v___x_1555_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1555_, 0, v___x_1553_);
                        lean_ctor_set(v___x_1555_, 1, v___x_1554_);
                        v___x_1556_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                        lean_ctor_set(v___x_1556_, 1, v___x_1552_);
                        v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
                        v___x_1558_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                        lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                        v___x_1559_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1559_, 0, v___x_1534_);
                        lean_ctor_set(v___x_1559_, 1, v___x_1550_);
                        v___x_1560_ = lean_box(0);
                        v___x_1561_ = lean_alloc_ctor(0, 6, (0) as u32);
                        lean_ctor_set(v___x_1561_, 0, v___x_1559_);
                        lean_ctor_set(v___x_1561_, 1, v___x_1560_);
                        lean_ctor_set(v___x_1561_, 2, v___x_1560_);
                        lean_ctor_set(v___x_1561_, 3, v___x_1560_);
                        lean_ctor_set(v___x_1561_, 4, v___x_1560_);
                        lean_ctor_set(v___x_1561_, 5, v___x_1560_);
                        v___x_1562_ = 0;
                        v___x_1563_ = lean_alloc_ctor(0, 3, (1) as u32);
                        lean_ctor_set(v___x_1563_, 0, v___x_1561_);
                        lean_ctor_set(v___x_1563_, 1, v___x_1560_);
                        lean_ctor_set(v___x_1563_, 2, v___x_1560_);
                        lean_ctor_set_uint8(
                            v___x_1563_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_1562_,
                        );
                        v___x_1564_ = lean_unsigned_to_nat(1);
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
                        lean_dec_ref(v___x_1566_);
                        if lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                            lean_inc(v_a_1568_);
                            lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1569_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1569_, 0, v_error_1511_);
                            lean_ctor_set(v___x_1569_, 1, v_a_1568_);
                            v___x_1570_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_1510_, v___x_1569_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
                            return v___x_1570_;
                        } else {
                            lean_dec_ref(v_error_1511_);
                            v_a_1571_ = lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1578_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1578_ == 0 {
                                v___x_1573_ = v___x_1567_;
                                v_isShared_1574_ = v_isSharedCheck_1578_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1571_);
                                lean_dec(v___x_1567_);
                                v___x_1573_ = lean_box(0);
                                v_isShared_1574_ = v_isSharedCheck_1578_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1528_);
                        lean_dec(v_name_1524_);
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
                    v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
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
    mut v___x_1582_: *mut LeanObject,
    mut v_t_1583_: *mut LeanObject,
    mut v_error_1584_: *mut LeanObject,
    mut v_loc_1585_: *mut LeanObject,
    mut v___y_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6770__boxed_1595_: u8 = 0;
    let mut v_res_1596_: *mut LeanObject = core::ptr::null_mut();
    v___x_6770__boxed_1595_ = (lean_unbox(v___x_1582_) as u8);
    v_res_1596_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6770__boxed_1595_, v_t_1583_, v_error_1584_, v_loc_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
    lean_dec(v___y_1593_);
    lean_dec_ref(v___y_1592_);
    lean_dec(v___y_1591_);
    lean_dec_ref(v___y_1590_);
    lean_dec(v___y_1589_);
    lean_dec_ref(v___y_1588_);
    lean_dec(v___y_1587_);
    lean_dec_ref(v___y_1586_);
    lean_dec(v_loc_1585_);
    lean_dec(v_t_1583_);
    return v_res_1596_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1()
-> *mut LeanObject {
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_error_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0;
    v_error_1599_ = l_Lean_stringToMessageData(v___x_1598_);
    return v_error_1599_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(
    mut v_t_1600_: *mut LeanObject,
    mut v_loc_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
    mut v_a_1603_: *mut LeanObject,
    mut v_a_1604_: *mut LeanObject,
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_error_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    v_error_1611_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
    v___x_1612_ = l_Lean_Syntax_isIdent(v_t_1600_);
    v___x_1613_ = lean_box((v___x_1612_) as usize);
    v___y_1614_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
    lean_closure_set(v___y_1614_, 0, v___x_1613_);
    lean_closure_set(v___y_1614_, 1, v_t_1600_);
    lean_closure_set(v___y_1614_, 2, v_error_1611_);
    lean_closure_set(v___y_1614_, 3, v_loc_1601_);
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
    mut v_t_1616_: *mut LeanObject,
    mut v_loc_1617_: *mut LeanObject,
    mut v_a_1618_: *mut LeanObject,
    mut v_a_1619_: *mut LeanObject,
    mut v_a_1620_: *mut LeanObject,
    mut v_a_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
    mut v_a_1624_: *mut LeanObject,
    mut v_a_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1627_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1625_);
    lean_dec_ref(v_a_1624_);
    lean_dec(v_a_1623_);
    lean_dec_ref(v_a_1622_);
    lean_dec(v_a_1621_);
    lean_dec_ref(v_a_1620_);
    lean_dec(v_a_1619_);
    lean_dec_ref(v_a_1618_);
    return v_res_1627_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(
    mut v_00_u03b1_1628_: *mut LeanObject,
    mut v_ref_1629_: *mut LeanObject,
    mut v_msg_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
    mut v___y_1637_: *mut LeanObject,
    mut v___y_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_1629_, v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(
    mut v_00_u03b1_1641_: *mut LeanObject,
    mut v_ref_1642_: *mut LeanObject,
    mut v_msg_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_res_1653_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_1641_, v_ref_1642_, v_msg_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
    lean_dec(v___y_1651_);
    lean_dec_ref(v___y_1650_);
    lean_dec(v___y_1649_);
    lean_dec_ref(v___y_1648_);
    lean_dec(v___y_1647_);
    lean_dec_ref(v___y_1646_);
    lean_dec(v___y_1645_);
    lean_dec_ref(v___y_1644_);
    lean_dec(v_ref_1642_);
    return v_res_1653_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(
    mut v_00_u03b1_1654_: *mut LeanObject,
    mut v_msg_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    v___x_1665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_1655_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
    return v___x_1665_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(
    mut v_00_u03b1_1666_: *mut LeanObject,
    mut v_msg_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1677_: *mut LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
    lean_dec(v___y_1675_);
    lean_dec_ref(v___y_1674_);
    lean_dec(v___y_1673_);
    lean_dec_ref(v___y_1672_);
    lean_dec(v___y_1671_);
    lean_dec_ref(v___y_1670_);
    lean_dec(v___y_1669_);
    lean_dec_ref(v___y_1668_);
    return v_res_1677_;
}
pub unsafe fn _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    v___x_1679_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0;
    v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(
    mut v_a_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1681_) == 0 {
                    v___x_1683_ = l_List_reverse___redArg(v_a_1682_);
                    return v___x_1683_;
                } else {
                    v_head_1684_ = lean_ctor_get(v_a_1681_, 0);
                    v_tail_1685_ = lean_ctor_get(v_a_1681_, 1);
                    v_isSharedCheck_1697_ = (!lean_is_exclusive(v_a_1681_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1687_ = v_a_1681_;
                        v_isShared_1688_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1685_);
                        lean_inc(v_head_1684_);
                        lean_dec(v_a_1681_);
                        v___x_1687_ = lean_box(0);
                        v_isShared_1688_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1689_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                v___x_1690_ = l_Lean_MessageData_ofSyntax(v_head_1684_);
                v___x_1691_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1691_, 0, v___x_1689_);
                lean_ctor_set(v___x_1691_, 1, v___x_1690_);
                v___x_1692_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1692_, 0, v___x_1691_);
                lean_ctor_set(v___x_1692_, 1, v___x_1689_);
                if v_isShared_1688_ == 0 {
                    lean_ctor_set(v___x_1687_, 1, v_a_1682_);
                    lean_ctor_set(v___x_1687_, 0, v___x_1692_);
                    v___x_1694_ = v___x_1687_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1692_);
                    lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1682_);
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
    mut v_msg_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1714_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1704_ = lean_ctor_get(v___y_1701_, 5);
                v___x_1705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
                v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
                v_isSharedCheck_1714_ = (!lean_is_exclusive(v___x_1705_)) as u8;
                if v_isSharedCheck_1714_ == 0 {
                    v___x_1708_ = v___x_1705_;
                    v_isShared_1709_ = v_isSharedCheck_1714_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1706_);
                    lean_dec(v___x_1705_);
                    v___x_1708_ = lean_box(0);
                    v_isShared_1709_ = v_isSharedCheck_1714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1704_);
                v___x_1710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1710_, 0, v_ref_1704_);
                lean_ctor_set(v___x_1710_, 1, v_a_1706_);
                if v_isShared_1709_ == 0 {
                    lean_ctor_set_tag(v___x_1708_, 1);
                    lean_ctor_set(v___x_1708_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
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
    mut v_msg_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
    lean_dec(v___y_1719_);
    lean_dec_ref(v___y_1718_);
    lean_dec(v___y_1717_);
    lean_dec_ref(v___y_1716_);
    return v_res_1721_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(
    mut v_ref_1722_: *mut LeanObject,
    mut v_msg_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1741_: u8 = 0;
    let mut v_cancelTk_x3f_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1743_: u8 = 0;
    let mut v_inheritedTraceOptions_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1729_ = lean_ctor_get(v___y_1726_, 0);
    v_fileMap_1730_ = lean_ctor_get(v___y_1726_, 1);
    v_options_1731_ = lean_ctor_get(v___y_1726_, 2);
    v_currRecDepth_1732_ = lean_ctor_get(v___y_1726_, 3);
    v_maxRecDepth_1733_ = lean_ctor_get(v___y_1726_, 4);
    v_ref_1734_ = lean_ctor_get(v___y_1726_, 5);
    v_currNamespace_1735_ = lean_ctor_get(v___y_1726_, 6);
    v_openDecls_1736_ = lean_ctor_get(v___y_1726_, 7);
    v_initHeartbeats_1737_ = lean_ctor_get(v___y_1726_, 8);
    v_maxHeartbeats_1738_ = lean_ctor_get(v___y_1726_, 9);
    v_quotContext_1739_ = lean_ctor_get(v___y_1726_, 10);
    v_currMacroScope_1740_ = lean_ctor_get(v___y_1726_, 11);
    v_diag_1741_ = lean_ctor_get_uint8(
        v___y_1726_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1742_ = lean_ctor_get(v___y_1726_, 12);
    v_suppressElabErrors_1743_ = lean_ctor_get_uint8(
        v___y_1726_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1744_ = lean_ctor_get(v___y_1726_, 13);
    v_ref_1745_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1734_);
    lean_inc_ref(v_inheritedTraceOptions_1744_);
    lean_inc(v_cancelTk_x3f_1742_);
    lean_inc(v_currMacroScope_1740_);
    lean_inc(v_quotContext_1739_);
    lean_inc(v_maxHeartbeats_1738_);
    lean_inc(v_initHeartbeats_1737_);
    lean_inc(v_openDecls_1736_);
    lean_inc(v_currNamespace_1735_);
    lean_inc(v_maxRecDepth_1733_);
    lean_inc(v_currRecDepth_1732_);
    lean_inc_ref(v_options_1731_);
    lean_inc_ref(v_fileMap_1730_);
    lean_inc_ref(v_fileName_1729_);
    v___x_1746_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1746_, 0, v_fileName_1729_);
    lean_ctor_set(v___x_1746_, 1, v_fileMap_1730_);
    lean_ctor_set(v___x_1746_, 2, v_options_1731_);
    lean_ctor_set(v___x_1746_, 3, v_currRecDepth_1732_);
    lean_ctor_set(v___x_1746_, 4, v_maxRecDepth_1733_);
    lean_ctor_set(v___x_1746_, 5, v_ref_1745_);
    lean_ctor_set(v___x_1746_, 6, v_currNamespace_1735_);
    lean_ctor_set(v___x_1746_, 7, v_openDecls_1736_);
    lean_ctor_set(v___x_1746_, 8, v_initHeartbeats_1737_);
    lean_ctor_set(v___x_1746_, 9, v_maxHeartbeats_1738_);
    lean_ctor_set(v___x_1746_, 10, v_quotContext_1739_);
    lean_ctor_set(v___x_1746_, 11, v_currMacroScope_1740_);
    lean_ctor_set(v___x_1746_, 12, v_cancelTk_x3f_1742_);
    lean_ctor_set(v___x_1746_, 13, v_inheritedTraceOptions_1744_);
    lean_ctor_set_uint8(
        v___x_1746_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1741_,
    );
    lean_ctor_set_uint8(
        v___x_1746_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1743_,
    );
    v___x_1747_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1723_, v___y_1724_, v___y_1725_, v___x_1746_, v___y_1727_);
    lean_dec_ref_known(v___x_1746_, 14);
    return v___x_1747_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(
    mut v_ref_1748_: *mut LeanObject,
    mut v_msg_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1755_: *mut LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_1748_, v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    lean_dec(v___y_1753_);
    lean_dec_ref(v___y_1752_);
    lean_dec(v___y_1751_);
    lean_dec_ref(v___y_1750_);
    lean_dec(v_ref_1748_);
    return v_res_1755_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0;
    v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1760_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2;
    v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    v___x_1763_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4;
    v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
    v___x_1766_ = l_Lean_MessageData_hint_x27(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___x_1771_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(
    mut v_stx_1775_: *mut LeanObject,
    mut v_simplifyTarget_1776_: u8,
    mut v_hyps_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
    mut v_a_1780_: *mut LeanObject,
    mut v_a_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypsStr_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_1787_ = lean_box(0);
                v___x_1788_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_1786_, v___x_1787_);
                v___x_1789_ = l_Lean_MessageData_andList(v___x_1788_);
                lean_inc_ref(v___y_1785_);
                v_hypsStr_1790_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_hypsStr_1790_, 0, v___y_1785_);
                lean_ctor_set(v_hypsStr_1790_, 1, v___x_1789_);
                v___x_1791_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
                lean_inc_ref(v___y_1784_);
                v___x_1792_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1792_, 0, v___y_1784_);
                v___x_1793_ = l_Lean_MessageData_ofFormat(v___x_1792_);
                v___x_1794_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1794_, 0, v___x_1793_);
                lean_ctor_set(v___x_1794_, 1, v_hypsStr_1790_);
                v___x_1795_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1795_, 0, v___x_1791_);
                lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                v___x_1796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
                v___x_1797_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1797_, 0, v___x_1795_);
                lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                v___x_1798_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
                v___x_1799_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1799_, 0, v___x_1797_);
                lean_ctor_set(v___x_1799_, 1, v___x_1798_);
                v___x_1800_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_1775_, v___x_1799_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
                return v___x_1800_;
            }
            2 => {
                v___x_1803_ = lean_array_get_size(v_hyps_1777_);
                v___x_1804_ = lean_unsigned_to_nat(1);
                v___x_1805_ = lean_nat_dec_eq(v___x_1803_, v___x_1804_);
                if v___x_1805_ == 0 {
                    v___x_1806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
                    v___y_1784_ = v___y_1802_;
                    v___y_1785_ = v___x_1806_;
                    state = 1;
                    continue;
                } else {
                    v___x_1807_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
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
    mut v_stx_1810_: *mut LeanObject,
    mut v_simplifyTarget_1811_: *mut LeanObject,
    mut v_hyps_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplifyTarget_boxed_1818_: u8 = 0;
    let mut v_res_1819_: *mut LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_1818_ = (lean_unbox(v_simplifyTarget_1811_) as u8);
    v_res_1819_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_1810_, v_simplifyTarget_boxed_1818_, v_hyps_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
    lean_dec(v_a_1816_);
    lean_dec_ref(v_a_1815_);
    lean_dec(v_a_1814_);
    lean_dec_ref(v_a_1813_);
    lean_dec(v_stx_1810_);
    return v_res_1819_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(
    mut v_stx_1820_: *mut LeanObject,
    mut v_simplifyTarget_1821_: u8,
    mut v_hyps_1822_: *mut LeanObject,
    mut v_00_u03b1_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    v___x_1829_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_1820_, v_simplifyTarget_1821_, v_hyps_1822_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
    return v___x_1829_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(
    mut v_stx_1830_: *mut LeanObject,
    mut v_simplifyTarget_1831_: *mut LeanObject,
    mut v_hyps_1832_: *mut LeanObject,
    mut v_00_u03b1_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_simplifyTarget_boxed_1839_: u8 = 0;
    let mut v_res_1840_: *mut LeanObject = core::ptr::null_mut();
    v_simplifyTarget_boxed_1839_ = (lean_unbox(v_simplifyTarget_1831_) as u8);
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
    lean_dec(v_a_1837_);
    lean_dec_ref(v_a_1836_);
    lean_dec(v_a_1835_);
    lean_dec_ref(v_a_1834_);
    lean_dec(v_stx_1830_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(
    mut v_00_u03b1_1841_: *mut LeanObject,
    mut v_ref_1842_: *mut LeanObject,
    mut v_msg_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_1842_, v_msg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(
    mut v_00_u03b1_1850_: *mut LeanObject,
    mut v_ref_1851_: *mut LeanObject,
    mut v_msg_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_1850_, v_ref_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
    lean_dec(v___y_1856_);
    lean_dec_ref(v___y_1855_);
    lean_dec(v___y_1854_);
    lean_dec_ref(v___y_1853_);
    lean_dec(v_ref_1851_);
    return v_res_1858_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(
    mut v_00_u03b1_1859_: *mut LeanObject,
    mut v_msg_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1866_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    return v___x_1866_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(
    mut v_00_u03b1_1867_: *mut LeanObject,
    mut v_msg_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1874_: *mut LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_1867_, v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
    lean_dec(v___y_1872_);
    lean_dec_ref(v___y_1871_);
    lean_dec(v___y_1870_);
    lean_dec_ref(v___y_1869_);
    return v_res_1874_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v___x_1876_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0;
    v___x_1877_ = l_Lean_stringToMessageData(v___x_1876_);
    return v___x_1877_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2;
    v___x_1880_ = l_Lean_stringToMessageData(v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(
    mut v_type_1890_: *mut LeanObject,
    mut v___x_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1907_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1917_ = l_Lean_Expr_getAppFn(v___x_1891_);
                if lean_obj_tag(v___x_1917_) == 4 {
                    v_declName_1918_ = lean_ctor_get(v___x_1917_, 0);
                    lean_inc_n(v_declName_1918_, 2);
                    lean_dec_ref_known(v___x_1917_, 2);
                    v___x_1919_ = lean_st_ref_get(v___y_1895_);
                    v_env_1920_ = lean_ctor_get(v___x_1919_, 0);
                    lean_inc_ref_n(v_env_1920_, 2);
                    lean_dec(v___x_1919_);
                    v___x_1921_ = l_Lean_isStructure(v_env_1920_, v_declName_1918_);
                    if v___x_1921_ == 0 {
                        lean_dec_ref(v_env_1920_);
                        lean_dec(v_declName_1918_);
                        v_a_1907_ = v___x_1921_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1922_ = lean_unsigned_to_nat(0);
                        v___x_1923_ = l_Lean_getStructureFields(v_env_1920_, v_declName_1918_);
                        v___x_1924_ = lean_array_get_size(v___x_1923_);
                        lean_dec_ref(v___x_1923_);
                        v___x_1925_ = lean_nat_dec_lt(v___x_1922_, v___x_1924_);
                        v_a_1907_ = v___x_1925_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1917_);
                    v___x_1926_ = 0;
                    v_a_1907_ = v___x_1926_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1899_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
                lean_inc_ref(v_val_1898_);
                v___x_1900_ = l_Lean_stringToMessageData(v_val_1898_);
                v___x_1901_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1901_, 0, v___x_1899_);
                lean_ctor_set(v___x_1901_, 1, v___x_1900_);
                v___x_1902_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
                v___x_1903_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1903_, 0, v___x_1901_);
                lean_ctor_set(v___x_1903_, 1, v___x_1902_);
                v___x_1904_ = l_Lean_MessageData_hint_x27(v___x_1903_);
                v___x_1905_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1905_, 0, v___x_1904_);
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
                            v___x_1913_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1913_, 0, v___x_1912_);
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
    mut v_type_1927_: *mut LeanObject,
    mut v___x_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(
            v_type_1927_,
            v___x_1928_,
            v___y_1929_,
            v___y_1930_,
            v___y_1931_,
            v___y_1932_,
        );
    lean_dec(v___y_1932_);
    lean_dec_ref(v___y_1931_);
    lean_dec(v___y_1930_);
    lean_dec_ref(v___y_1929_);
    lean_dec_ref(v___x_1928_);
    lean_dec_ref(v_type_1927_);
    return v_res_1934_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(
    mut v_type_1935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    v___x_1936_ = l_Lean_Expr_getAppFn(v_type_1935_);
    v___f_1937_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___f_1937_, 0, v_type_1935_);
    lean_closure_set(v___f_1937_, 1, v___x_1936_);
    v___x_1938_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5;
    v___x_1939_ = l_Lean_MessageData_ofLazyM(v___f_1937_, v___x_1938_);
    return v___x_1939_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2()
-> *mut LeanObject {
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1;
    v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(
    mut v_mvarId_1945_: *mut LeanObject,
    mut v_a_1946_: *mut LeanObject,
    mut v_a_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_1945_);
                v___x_1951_ = l_Lean_MVarId_getType(
                    v_mvarId_1945_,
                    v_a_1946_,
                    v_a_1947_,
                    v_a_1948_,
                    v_a_1949_,
                );
                if lean_obj_tag(v___x_1951_) == 0 {
                    v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
                    lean_inc(v_a_1952_);
                    lean_dec_ref_known(v___x_1951_, 1);
                    v___x_1953_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_1952_);
                    v___x_1954_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
                    v___x_1955_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
                    v___x_1956_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1956_, 0, v___x_1955_);
                    lean_ctor_set(v___x_1956_, 1, v___x_1953_);
                    v___x_1957_ =
                        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
                    v___x_1958_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1958_, 0, v___x_1956_);
                    lean_ctor_set(v___x_1958_, 1, v___x_1957_);
                    v___x_1959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1959_, 0, v___x_1958_);
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
                    lean_dec(v_mvarId_1945_);
                    v_a_1961_ = lean_ctor_get(v___x_1951_, 0);
                    v_isSharedCheck_1968_ = (!lean_is_exclusive(v___x_1951_)) as u8;
                    if v_isSharedCheck_1968_ == 0 {
                        v___x_1963_ = v___x_1951_;
                        v_isShared_1964_ = v_isSharedCheck_1968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1961_);
                        lean_dec(v___x_1951_);
                        v___x_1963_ = lean_box(0);
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
                    v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
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
    mut v_mvarId_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(
            v_mvarId_1969_,
            v_a_1970_,
            v_a_1971_,
            v_a_1972_,
            v_a_1973_,
        );
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    lean_dec(v_a_1971_);
    lean_dec_ref(v_a_1970_);
    return v_res_1975_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1()
-> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0;
    v___x_1978_ = l_Lean_stringToMessageData(v___x_1977_);
    return v___x_1978_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3()
-> *mut LeanObject {
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    v___x_1980_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2;
    v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
    return v___x_1981_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(
    mut v_fvarId_1982_: *mut LeanObject,
    mut v_mvarId_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
    mut v_a_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_1982_);
                v___x_1989_ =
                    l_Lean_FVarId_getType___redArg(v_fvarId_1982_, v_a_1984_, v_a_1986_, v_a_1987_);
                if lean_obj_tag(v___x_1989_) == 0 {
                    v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
                    lean_inc_n(v_a_1990_, 2);
                    lean_dec_ref_known(v___x_1989_, 1);
                    v___x_1991_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
                    v___x_1992_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1);
                    v___x_1993_ = lean_unsigned_to_nat(30);
                    v___x_1994_ = l_Lean_inlineExpr(v_a_1990_, v___x_1993_);
                    v___x_1995_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1995_, 0, v___x_1992_);
                    lean_ctor_set(v___x_1995_, 1, v___x_1994_);
                    v___x_1996_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3);
                    v___x_1997_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1997_, 0, v___x_1995_);
                    lean_ctor_set(v___x_1997_, 1, v___x_1996_);
                    v___x_1998_ = l_Lean_Expr_fvar___override(v_fvarId_1982_);
                    v___x_1999_ = l_Lean_MessageData_ofExpr(v___x_1998_);
                    v___x_2000_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2000_, 0, v___x_1997_);
                    lean_ctor_set(v___x_2000_, 1, v___x_1999_);
                    v___x_2001_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                    v___x_2002_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2002_, 0, v___x_2000_);
                    lean_ctor_set(v___x_2002_, 1, v___x_2001_);
                    v___x_2003_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_1990_);
                    v___x_2004_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2004_, 0, v___x_2002_);
                    lean_ctor_set(v___x_2004_, 1, v___x_2003_);
                    v___x_2005_ =
                        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
                    v___x_2006_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2006_, 0, v___x_2004_);
                    lean_ctor_set(v___x_2006_, 1, v___x_2005_);
                    v___x_2007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2007_, 0, v___x_2006_);
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
                    lean_dec(v_mvarId_1983_);
                    lean_dec(v_fvarId_1982_);
                    v_a_2009_ = lean_ctor_get(v___x_1989_, 0);
                    v_isSharedCheck_2016_ = (!lean_is_exclusive(v___x_1989_)) as u8;
                    if v_isSharedCheck_2016_ == 0 {
                        v___x_2011_ = v___x_1989_;
                        v_isShared_2012_ = v_isSharedCheck_2016_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2009_);
                        lean_dec(v___x_1989_);
                        v___x_2011_ = lean_box(0);
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
                    v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
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
    mut v_fvarId_2017_: *mut LeanObject,
    mut v_mvarId_2018_: *mut LeanObject,
    mut v_a_2019_: *mut LeanObject,
    mut v_a_2020_: *mut LeanObject,
    mut v_a_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2024_: *mut LeanObject = core::ptr::null_mut();
    v_res_2024_ =
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(
            v_fvarId_2017_,
            v_mvarId_2018_,
            v_a_2019_,
            v_a_2020_,
            v_a_2021_,
            v_a_2022_,
        );
    lean_dec(v_a_2022_);
    lean_dec_ref(v_a_2021_);
    lean_dec(v_a_2020_);
    lean_dec_ref(v_a_2019_);
    return v_res_2024_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2025_) == 0 {
                    v___x_2027_ = l_List_reverse___redArg(v_a_2026_);
                    return v___x_2027_;
                } else {
                    v_head_2028_ = lean_ctor_get(v_a_2025_, 0);
                    v_tail_2029_ = lean_ctor_get(v_a_2025_, 1);
                    v_isSharedCheck_2042_ = (!lean_is_exclusive(v_a_2025_)) as u8;
                    if v_isSharedCheck_2042_ == 0 {
                        v___x_2031_ = v_a_2025_;
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2029_);
                        lean_inc(v_head_2028_);
                        lean_dec(v_a_2025_);
                        v___x_2031_ = lean_box(0);
                        v_isShared_2032_ = v_isSharedCheck_2042_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2033_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1), core::ptr::addr_of_mut!(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once), _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
                v___x_2034_ = l_Lean_Expr_fvar___override(v_head_2028_);
                v___x_2035_ = l_Lean_MessageData_ofExpr(v___x_2034_);
                v___x_2036_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2036_, 0, v___x_2033_);
                lean_ctor_set(v___x_2036_, 1, v___x_2035_);
                v___x_2037_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2037_, 0, v___x_2036_);
                lean_ctor_set(v___x_2037_, 1, v___x_2033_);
                if v_isShared_2032_ == 0 {
                    lean_ctor_set(v___x_2031_, 1, v_a_2026_);
                    lean_ctor_set(v___x_2031_, 0, v___x_2037_);
                    v___x_2039_ = v___x_2031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2037_);
                    lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2026_);
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
-> *mut LeanObject {
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    v___x_2046_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1;
    v___x_2047_ = l_Lean_MessageData_ofFormat(v___x_2046_);
    return v___x_2047_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_note_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2048_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
    v_note_2049_ = l_Lean_MessageData_note(v___x_2048_);
    return v_note_2049_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4;
    v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6()
-> *mut LeanObject {
    let mut v_note_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    v_note_2053_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
    v___x_2054_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
    v___x_2055_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2055_, 0, v___x_2054_);
    lean_ctor_set(v___x_2055_, 1, v_note_2053_);
    return v___x_2055_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v___x_2056_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
    v___x_2057_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
    v___x_2058_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    lean_ctor_set(v___x_2058_, 1, v___x_2056_);
    return v___x_2058_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
    v___x_2060_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    return v___x_2060_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___x_2064_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10;
    v___x_2065_ = l_Lean_MessageData_ofFormat(v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    v___x_2067_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12;
    v___x_2068_ = l_Lean_stringToMessageData(v___x_2067_);
    return v___x_2068_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(
    mut v_fvarIds_2069_: *mut LeanObject,
    mut v_mvarId_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_note_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    v_note_2076_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
    v___x_2077_ = lean_unsigned_to_nat(0);
    v___x_2078_ = lean_array_get_size(v_fvarIds_2069_);
    v___x_2079_ = lean_nat_dec_lt(v___x_2077_, v___x_2078_);
    if v___x_2079_ == 0 {
        let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_fvarIds_2069_);
        v___x_2080_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
        v___x_2081_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
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
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fvarMsgs_2085_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fvarMsgs_2087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
        v___x_2083_ = lean_array_to_list(v_fvarIds_2069_);
        v___x_2084_ = lean_box(0);
        v_fvarMsgs_2085_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_2083_, v___x_2084_);
        v___x_2086_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
        v_fvarMsgs_2087_ = l_Lean_MessageData_joinSep(v_fvarMsgs_2085_, v___x_2086_);
        v___x_2088_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0;
        v___x_2089_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
        v___x_2090_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2090_, 0, v___x_2089_);
        lean_ctor_set(v___x_2090_, 1, v_fvarMsgs_2087_);
        v___x_2091_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2091_, 0, v___x_2090_);
        lean_ctor_set(v___x_2091_, 1, v_note_2076_);
        v___x_2092_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
        v___x_2093_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_2093_, 0, v___x_2091_);
        lean_ctor_set(v___x_2093_, 1, v___x_2092_);
        v___x_2094_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2094_, 0, v___x_2093_);
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
    mut v_fvarIds_2096_: *mut LeanObject,
    mut v_mvarId_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2103_: *mut LeanObject = core::ptr::null_mut();
    v_res_2103_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_2096_, v_mvarId_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
    lean_dec(v_a_2101_);
    lean_dec_ref(v_a_2100_);
    lean_dec(v_a_2099_);
    lean_dec_ref(v_a_2098_);
    return v_res_2103_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(
    mut v_00_u03b1_2104_: *mut LeanObject,
    mut v_fvarIds_2105_: *mut LeanObject,
    mut v_mvarId_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_2105_, v_mvarId_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
    return v___x_2112_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(
    mut v_00_u03b1_2113_: *mut LeanObject,
    mut v_fvarIds_2114_: *mut LeanObject,
    mut v_mvarId_2115_: *mut LeanObject,
    mut v_a_2116_: *mut LeanObject,
    mut v_a_2117_: *mut LeanObject,
    mut v_a_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2121_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2119_);
    lean_dec_ref(v_a_2118_);
    lean_dec(v_a_2117_);
    lean_dec_ref(v_a_2116_);
    return v_res_2121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(
    mut v_a_2125_: *mut LeanObject,
    mut v_as_2126_: *mut LeanObject,
    mut v_sz_2127_: usize,
    mut v_i_2128_: usize,
    mut v_b_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
    mut v___y_2131_: *mut LeanObject,
    mut v___y_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: usize = 0;
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2135_ = lean_usize_dec_lt(v_i_2128_, v_sz_2127_);
                if v___x_2135_ == 0 {
                    lean_dec(v_a_2125_);
                    v___x_2136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2136_, 0, v_b_2129_);
                    return v___x_2136_;
                } else {
                    lean_dec_ref(v_b_2129_);
                    v_a_2137_ = lean_array_uget_borrowed(v_as_2126_, v_i_2128_);
                    lean_inc(v_a_2137_);
                    lean_inc(v_a_2125_);
                    v___x_2138_ = l_Lean_Meta_splitLocalDecl_x3f(
                        v_a_2125_,
                        v_a_2137_,
                        v___y_2130_,
                        v___y_2131_,
                        v___y_2132_,
                        v___y_2133_,
                    );
                    if lean_obj_tag(v___x_2138_) == 0 {
                        v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
                        v_isSharedCheck_2152_ = (!lean_is_exclusive(v___x_2138_)) as u8;
                        if v_isSharedCheck_2152_ == 0 {
                            v___x_2141_ = v___x_2138_;
                            v_isShared_2142_ = v_isSharedCheck_2152_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2139_);
                            lean_dec(v___x_2138_);
                            v___x_2141_ = lean_box(0);
                            v_isShared_2142_ = v_isSharedCheck_2152_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2125_);
                        v_a_2153_ = lean_ctor_get(v___x_2138_, 0);
                        v_isSharedCheck_2160_ = (!lean_is_exclusive(v___x_2138_)) as u8;
                        if v_isSharedCheck_2160_ == 0 {
                            v___x_2155_ = v___x_2138_;
                            v_isShared_2156_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2153_);
                            lean_dec(v___x_2138_);
                            v___x_2155_ = lean_box(0);
                            v_isShared_2156_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2143_ = lean_box(0);
                if lean_obj_tag(v_a_2139_) == 1 {
                    lean_dec(v_a_2125_);
                    v___x_2144_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2144_, 0, v_a_2139_);
                    lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                    if v_isShared_2142_ == 0 {
                        lean_ctor_set(v___x_2141_, 0, v___x_2144_);
                        v___x_2146_ = v___x_2141_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
                        v___x_2146_ = v_reuseFailAlloc_2147_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2141_);
                    lean_dec(v_a_2139_);
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
                    v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
    mut v_a_2161_: *mut LeanObject,
    mut v_as_2162_: *mut LeanObject,
    mut v_sz_2163_: *mut LeanObject,
    mut v_i_2164_: *mut LeanObject,
    mut v_b_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
    mut v___y_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2171_: usize = 0;
    let mut v_i_boxed_2172_: usize = 0;
    let mut v_res_2173_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2171_ = lean_unbox_usize(v_sz_2163_);
    lean_dec(v_sz_2163_);
    v_i_boxed_2172_ = lean_unbox_usize(v_i_2164_);
    lean_dec(v_i_2164_);
    v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_2161_, v_as_2162_, v_sz_boxed_2171_, v_i_boxed_2172_, v_b_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
    lean_dec(v___y_2169_);
    lean_dec_ref(v___y_2168_);
    lean_dec(v___y_2167_);
    lean_dec_ref(v___y_2166_);
    lean_dec_ref(v_as_2162_);
    return v_res_2173_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__0(
    mut v___y_2174_: *mut LeanObject,
    mut v___y_2175_: *mut LeanObject,
    mut v___y_2176_: *mut LeanObject,
    mut v___y_2177_: *mut LeanObject,
    mut v___y_2178_: *mut LeanObject,
    mut v___y_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_unused_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2200_: usize = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_a_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_val_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_a_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_a_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2195_) == 0 {
                    v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
                    lean_inc_n(v_a_2196_, 2);
                    lean_dec_ref_known(v___x_2195_, 1);
                    v___x_2197_ = l_Lean_MVarId_getNondepPropHyps(
                        v_a_2196_,
                        v___y_2178_,
                        v___y_2179_,
                        v___y_2180_,
                        v___y_2181_,
                    );
                    if lean_obj_tag(v___x_2197_) == 0 {
                        v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
                        lean_inc(v_a_2198_);
                        lean_dec_ref_known(v___x_2197_, 1);
                        v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0;
                        v_sz_2200_ = lean_array_size(v_a_2198_);
                        v___x_2201_ = 0usize;
                        lean_inc(v_a_2196_);
                        v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_2196_, v_a_2198_, v_sz_2200_, v___x_2201_, v___x_2199_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
                        if lean_obj_tag(v___x_2202_) == 0 {
                            v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
                            lean_inc(v_a_2203_);
                            lean_dec_ref_known(v___x_2202_, 1);
                            v_fst_2204_ = lean_ctor_get(v_a_2203_, 0);
                            lean_inc(v_fst_2204_);
                            lean_dec(v_a_2203_);
                            if lean_obj_tag(v_fst_2204_) == 0 {
                                v___x_2205_ = 1;
                                v___x_2206_ = 0;
                                lean_inc(v_a_2196_);
                                v___x_2207_ = l_Lean_Meta_splitTarget_x3f(
                                    v_a_2196_,
                                    v___x_2205_,
                                    v___x_2206_,
                                    v___y_2178_,
                                    v___y_2179_,
                                    v___y_2180_,
                                    v___y_2181_,
                                );
                                if lean_obj_tag(v___x_2207_) == 0 {
                                    v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
                                    lean_inc(v_a_2208_);
                                    lean_dec_ref_known(v___x_2207_, 1);
                                    if lean_obj_tag(v_a_2208_) == 1 {
                                        lean_dec(v_a_2198_);
                                        lean_dec(v_a_2196_);
                                        v_val_2209_ = lean_ctor_get(v_a_2208_, 0);
                                        lean_inc(v_val_2209_);
                                        lean_dec_ref_known(v_a_2208_, 1);
                                        v_a_2184_ = v_val_2209_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_2208_);
                                        v___x_2210_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_2198_, v_a_2196_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
                                        if lean_obj_tag(v___x_2210_) == 0 {
                                            v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
                                            lean_inc(v_a_2211_);
                                            lean_dec_ref_known(v___x_2210_, 1);
                                            v_a_2184_ = v_a_2211_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_a_2212_ = lean_ctor_get(v___x_2210_, 0);
                                            v_isSharedCheck_2219_ =
                                                (!lean_is_exclusive(v___x_2210_)) as u8;
                                            if v_isSharedCheck_2219_ == 0 {
                                                v___x_2214_ = v___x_2210_;
                                                v_isShared_2215_ = v_isSharedCheck_2219_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2212_);
                                                lean_dec(v___x_2210_);
                                                v___x_2214_ = lean_box(0);
                                                v_isShared_2215_ = v_isSharedCheck_2219_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2198_);
                                    lean_dec(v_a_2196_);
                                    v_a_2220_ = lean_ctor_get(v___x_2207_, 0);
                                    v_isSharedCheck_2227_ = (!lean_is_exclusive(v___x_2207_)) as u8;
                                    if v_isSharedCheck_2227_ == 0 {
                                        v___x_2222_ = v___x_2207_;
                                        v_isShared_2223_ = v_isSharedCheck_2227_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2220_);
                                        lean_dec(v___x_2207_);
                                        v___x_2222_ = lean_box(0);
                                        v_isShared_2223_ = v_isSharedCheck_2227_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2198_);
                                lean_dec(v_a_2196_);
                                v_val_2228_ = lean_ctor_get(v_fst_2204_, 0);
                                lean_inc(v_val_2228_);
                                lean_dec_ref_known(v_fst_2204_, 1);
                                v_a_2184_ = v_val_2228_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2198_);
                            lean_dec(v_a_2196_);
                            v_a_2229_ = lean_ctor_get(v___x_2202_, 0);
                            v_isSharedCheck_2236_ = (!lean_is_exclusive(v___x_2202_)) as u8;
                            if v_isSharedCheck_2236_ == 0 {
                                v___x_2231_ = v___x_2202_;
                                v_isShared_2232_ = v_isSharedCheck_2236_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2229_);
                                lean_dec(v___x_2202_);
                                v___x_2231_ = lean_box(0);
                                v_isShared_2232_ = v_isSharedCheck_2236_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2196_);
                        v_a_2237_ = lean_ctor_get(v___x_2197_, 0);
                        v_isSharedCheck_2244_ = (!lean_is_exclusive(v___x_2197_)) as u8;
                        if v_isSharedCheck_2244_ == 0 {
                            v___x_2239_ = v___x_2197_;
                            v_isShared_2240_ = v_isSharedCheck_2244_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2237_);
                            lean_dec(v___x_2197_);
                            v___x_2239_ = lean_box(0);
                            v_isShared_2240_ = v_isSharedCheck_2244_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_a_2245_ = lean_ctor_get(v___x_2195_, 0);
                    v_isSharedCheck_2252_ = (!lean_is_exclusive(v___x_2195_)) as u8;
                    if v_isSharedCheck_2252_ == 0 {
                        v___x_2247_ = v___x_2195_;
                        v_isShared_2248_ = v_isSharedCheck_2252_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2245_);
                        lean_dec(v___x_2195_);
                        v___x_2247_ = lean_box(0);
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
                if lean_obj_tag(v___x_2185_) == 0 {
                    v_isSharedCheck_2193_ = (!lean_is_exclusive(v___x_2185_)) as u8;
                    if v_isSharedCheck_2193_ == 0 {
                        v_unused_2194_ = lean_ctor_get(v___x_2185_, 0);
                        lean_dec(v_unused_2194_);
                        v___x_2187_ = v___x_2185_;
                        v_isShared_2188_ = v_isSharedCheck_2193_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2185_);
                        v___x_2187_ = lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2193_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2185_;
                }
            }
            2 => {
                v___x_2189_ = lean_box(0);
                if v_isShared_2188_ == 0 {
                    lean_ctor_set(v___x_2187_, 0, v___x_2189_);
                    v___x_2191_ = v___x_2187_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2189_);
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
                    v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
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
                    v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
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
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
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
                    v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
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
                    v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
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
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2262_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2260_);
    lean_dec_ref(v___y_2259_);
    lean_dec(v___y_2258_);
    lean_dec_ref(v___y_2257_);
    lean_dec(v___y_2256_);
    lean_dec_ref(v___y_2255_);
    lean_dec(v___y_2254_);
    lean_dec_ref(v___y_2253_);
    return v_res_2262_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__1(
    mut v_type_2263_: u8,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v_unused_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2300_: u8 = 0;
    let mut v_a_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2304_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut v_a_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2312_: u8 = 0;
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2315_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2285_) == 0 {
                    v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
                    lean_inc_n(v_a_2286_, 2);
                    lean_dec_ref_known(v___x_2285_, 1);
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
                    if lean_obj_tag(v___x_2288_) == 0 {
                        v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
                        lean_inc(v_a_2289_);
                        lean_dec_ref_known(v___x_2288_, 1);
                        if lean_obj_tag(v_a_2289_) == 1 {
                            lean_dec(v_a_2286_);
                            v_val_2290_ = lean_ctor_get(v_a_2289_, 0);
                            lean_inc(v_val_2290_);
                            lean_dec_ref_known(v_a_2289_, 1);
                            v_a_2274_ = v_val_2290_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2289_);
                            v___x_2291_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_2286_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
                            if lean_obj_tag(v___x_2291_) == 0 {
                                v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
                                lean_inc(v_a_2292_);
                                lean_dec_ref_known(v___x_2291_, 1);
                                v_a_2274_ = v_a_2292_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2293_ = lean_ctor_get(v___x_2291_, 0);
                                v_isSharedCheck_2300_ = (!lean_is_exclusive(v___x_2291_)) as u8;
                                if v_isSharedCheck_2300_ == 0 {
                                    v___x_2295_ = v___x_2291_;
                                    v_isShared_2296_ = v_isSharedCheck_2300_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2293_);
                                    lean_dec(v___x_2291_);
                                    v___x_2295_ = lean_box(0);
                                    v_isShared_2296_ = v_isSharedCheck_2300_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2286_);
                        v_a_2301_ = lean_ctor_get(v___x_2288_, 0);
                        v_isSharedCheck_2308_ = (!lean_is_exclusive(v___x_2288_)) as u8;
                        if v_isSharedCheck_2308_ == 0 {
                            v___x_2303_ = v___x_2288_;
                            v_isShared_2304_ = v_isSharedCheck_2308_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2301_);
                            lean_dec(v___x_2288_);
                            v___x_2303_ = lean_box(0);
                            v_isShared_2304_ = v_isSharedCheck_2308_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_2309_ = lean_ctor_get(v___x_2285_, 0);
                    v_isSharedCheck_2316_ = (!lean_is_exclusive(v___x_2285_)) as u8;
                    if v_isSharedCheck_2316_ == 0 {
                        v___x_2311_ = v___x_2285_;
                        v_isShared_2312_ = v_isSharedCheck_2316_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2309_);
                        lean_dec(v___x_2285_);
                        v___x_2311_ = lean_box(0);
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
                if lean_obj_tag(v___x_2275_) == 0 {
                    v_isSharedCheck_2283_ = (!lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2283_ == 0 {
                        v_unused_2284_ = lean_ctor_get(v___x_2275_, 0);
                        lean_dec(v_unused_2284_);
                        v___x_2277_ = v___x_2275_;
                        v_isShared_2278_ = v_isSharedCheck_2283_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2275_);
                        v___x_2277_ = lean_box(0);
                        v_isShared_2278_ = v_isSharedCheck_2283_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2275_;
                }
            }
            2 => {
                v___x_2279_ = lean_box(0);
                if v_isShared_2278_ == 0 {
                    lean_ctor_set(v___x_2277_, 0, v___x_2279_);
                    v___x_2281_ = v___x_2277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2279_);
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
                    v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
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
                    v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
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
                    v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
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
    mut v_type_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
    mut v___y_2319_: *mut LeanObject,
    mut v___y_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_4513__boxed_2327_: u8 = 0;
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_type_4513__boxed_2327_ = (lean_unbox(v_type_2317_) as u8);
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
    lean_dec(v___y_2325_);
    lean_dec_ref(v___y_2324_);
    lean_dec(v___y_2323_);
    lean_dec_ref(v___y_2322_);
    lean_dec(v___y_2321_);
    lean_dec_ref(v___y_2320_);
    lean_dec(v___y_2319_);
    lean_dec_ref(v___y_2318_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___lam__2(
    mut v_a_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v_unused_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_a_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_a_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
                    lean_inc_n(v_a_2352_, 2);
                    lean_dec_ref_known(v___x_2351_, 1);
                    lean_inc(v_a_2329_);
                    v___x_2353_ = l_Lean_Meta_splitLocalDecl_x3f(
                        v_a_2352_,
                        v_a_2329_,
                        v___y_2334_,
                        v___y_2335_,
                        v___y_2336_,
                        v___y_2337_,
                    );
                    if lean_obj_tag(v___x_2353_) == 0 {
                        v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
                        lean_inc(v_a_2354_);
                        lean_dec_ref_known(v___x_2353_, 1);
                        if lean_obj_tag(v_a_2354_) == 1 {
                            lean_dec(v_a_2352_);
                            lean_dec(v_a_2329_);
                            v_val_2355_ = lean_ctor_get(v_a_2354_, 0);
                            lean_inc(v_val_2355_);
                            lean_dec_ref_known(v_a_2354_, 1);
                            v_a_2340_ = v_val_2355_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2354_);
                            v___x_2356_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_2329_, v_a_2352_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
                            if lean_obj_tag(v___x_2356_) == 0 {
                                v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
                                lean_inc(v_a_2357_);
                                lean_dec_ref_known(v___x_2356_, 1);
                                v_a_2340_ = v_a_2357_;
                                state = 1;
                                continue;
                            } else {
                                v_a_2358_ = lean_ctor_get(v___x_2356_, 0);
                                v_isSharedCheck_2365_ = (!lean_is_exclusive(v___x_2356_)) as u8;
                                if v_isSharedCheck_2365_ == 0 {
                                    v___x_2360_ = v___x_2356_;
                                    v_isShared_2361_ = v_isSharedCheck_2365_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2358_);
                                    lean_dec(v___x_2356_);
                                    v___x_2360_ = lean_box(0);
                                    v_isShared_2361_ = v_isSharedCheck_2365_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2352_);
                        lean_dec(v_a_2329_);
                        v_a_2366_ = lean_ctor_get(v___x_2353_, 0);
                        v_isSharedCheck_2373_ = (!lean_is_exclusive(v___x_2353_)) as u8;
                        if v_isSharedCheck_2373_ == 0 {
                            v___x_2368_ = v___x_2353_;
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2366_);
                            lean_dec(v___x_2353_);
                            v___x_2368_ = lean_box(0);
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2329_);
                    v_a_2374_ = lean_ctor_get(v___x_2351_, 0);
                    v_isSharedCheck_2381_ = (!lean_is_exclusive(v___x_2351_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v___x_2376_ = v___x_2351_;
                        v_isShared_2377_ = v_isSharedCheck_2381_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2374_);
                        lean_dec(v___x_2351_);
                        v___x_2376_ = lean_box(0);
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
                if lean_obj_tag(v___x_2341_) == 0 {
                    v_isSharedCheck_2349_ = (!lean_is_exclusive(v___x_2341_)) as u8;
                    if v_isSharedCheck_2349_ == 0 {
                        v_unused_2350_ = lean_ctor_get(v___x_2341_, 0);
                        lean_dec(v_unused_2350_);
                        v___x_2343_ = v___x_2341_;
                        v_isShared_2344_ = v_isSharedCheck_2349_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2341_);
                        v___x_2343_ = lean_box(0);
                        v_isShared_2344_ = v_isSharedCheck_2349_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2341_;
                }
            }
            2 => {
                v___x_2345_ = lean_box(0);
                if v_isShared_2344_ == 0 {
                    lean_ctor_set(v___x_2343_, 0, v___x_2345_);
                    v___x_2347_ = v___x_2343_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
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
                    v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
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
                    v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
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
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
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
    mut v_a_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2392_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2390_);
    lean_dec_ref(v___y_2389_);
    lean_dec(v___y_2388_);
    lean_dec_ref(v___y_2387_);
    lean_dec(v___y_2386_);
    lean_dec_ref(v___y_2385_);
    lean_dec(v___y_2384_);
    lean_dec_ref(v___y_2383_);
    return v_res_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit(
    mut v_stx_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
    mut v_a_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2406_: u8 = 0;
    let mut v___y_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2430_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: u8 = 0;
    let mut v___y_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2448_: u8 = 0;
    let mut v___y_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2459_: u8 = 0;
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___f_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_loc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hypotheses_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2478_: u8 = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: u8 = 0;
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: u8 = 0;
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: u8 = 0;
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u8 = 0;
    let mut v_loc_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2463_ = l_Lean_Elab_Tactic_evalSplit___closed__0;
                v___x_2484_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
                lean_inc(v_stx_2394_);
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
                    v___x_2486_ = lean_unsigned_to_nat(1);
                    v___x_2487_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2486_);
                    lean_inc(v___x_2487_);
                    v___x_2488_ = l_Lean_Syntax_matchesNull(v___x_2487_, v___x_2486_);
                    if v___x_2488_ == 0 {
                        lean_dec(v___x_2487_);
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
                        v___x_2489_ = lean_unsigned_to_nat(0);
                        v_t_2490_ = l_Lean_Syntax_getArg(v___x_2487_, v___x_2489_);
                        lean_dec(v___x_2487_);
                        v___x_2502_ = lean_unsigned_to_nat(2);
                        v___x_2503_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2502_);
                        v___x_2504_ = l_Lean_Syntax_isNone(v___x_2503_);
                        if v___x_2504_ == 0 {
                            lean_inc(v___x_2503_);
                            v___x_2505_ = l_Lean_Syntax_matchesNull(v___x_2503_, v___x_2486_);
                            if v___x_2505_ == 0 {
                                lean_dec(v___x_2503_);
                                lean_dec(v_t_2490_);
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
                                lean_dec(v___x_2503_);
                                v___x_2507_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10;
                                lean_inc(v___x_2506_);
                                v___x_2508_ = l_Lean_Syntax_isOfKind(v___x_2506_, v___x_2507_);
                                if v___x_2508_ == 0 {
                                    lean_dec(v___x_2506_);
                                    lean_dec(v_t_2490_);
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
                                    lean_dec(v___x_2506_);
                                    v___x_2510_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_2510_, 0, v_loc_2509_);
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
                            lean_dec(v___x_2503_);
                            v___x_2511_ = lean_box(0);
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
                    lean_dec_ref(v___y_2405_);
                    v___x_2416_ = lean_box(0);
                    v___x_2417_ = lean_unsigned_to_nat(0);
                    v___x_2418_ = lean_array_get(v___x_2416_, v___y_2407_, v___x_2417_);
                    lean_dec_ref(v___y_2407_);
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
                    if lean_obj_tag(v___x_2419_) == 0 {
                        v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
                        lean_inc(v_a_2420_);
                        lean_dec_ref_known(v___x_2419_, 1);
                        v___f_2421_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_evalSplit___lam__2___boxed as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        lean_closure_set(v___f_2421_, 0, v_a_2420_);
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
                        v_a_2423_ = lean_ctor_get(v___x_2419_, 0);
                        v_isSharedCheck_2430_ = (!lean_is_exclusive(v___x_2419_)) as u8;
                        if v_isSharedCheck_2430_ == 0 {
                            v___x_2425_ = v___x_2419_;
                            v_isShared_2426_ = v_isSharedCheck_2430_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2423_);
                            lean_dec(v___x_2419_);
                            v___x_2425_ = lean_box(0);
                            v_isShared_2426_ = v_isSharedCheck_2430_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2407_);
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
                    v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
                    v___x_2428_ = v_reuseFailAlloc_2429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2428_;
            }
            4 => {
                lean_dec_ref(v___y_2433_);
                v___x_2445_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_2442_, v___y_2440_, v___y_2444_, v___y_2439_, v___y_2441_, v___y_2437_, v___y_2443_);
                lean_dec(v___y_2442_);
                return v___x_2445_;
            }
            5 => {
                if v___y_2459_ == 0 {
                    v___x_2460_ = lean_unsigned_to_nat(1);
                    v___x_2461_ = lean_array_get_size(v___y_2449_);
                    v___x_2462_ = lean_nat_dec_lt(v___x_2460_, v___x_2461_);
                    if v___x_2462_ == 0 {
                        lean_dec(v___y_2457_);
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
                v___x_2473_ = lean_unsigned_to_nat(2);
                v___x_2474_ = l_Lean_Syntax_getArg(v_stx_2394_, v___x_2473_);
                lean_dec(v_stx_2394_);
                v_loc_2475_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_2474_);
                if lean_obj_tag(v_loc_2475_) == 0 {
                    lean_dec(v___x_2474_);
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
                    v_hypotheses_2477_ = lean_ctor_get(v_loc_2475_, 0);
                    lean_inc_ref(v_hypotheses_2477_);
                    v_type_2478_ = lean_ctor_get_uint8(
                        v_loc_2475_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_loc_2475_, 1);
                    v___x_2479_ = lean_box((v_type_2478_) as usize);
                    v___f_2480_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalSplit___lam__1___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_2480_, 0, v___x_2479_);
                    v___x_2481_ = lean_unsigned_to_nat(0);
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
                if lean_obj_tag(v___x_2501_) == 0 {
                    lean_dec_ref_known(v___x_2501_, 1);
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
                    lean_dec(v_stx_2394_);
                    return v___x_2501_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalSplit___boxed(
    mut v_stx_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
    mut v_a_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2522_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2520_);
    lean_dec_ref(v_a_2519_);
    lean_dec(v_a_2518_);
    lean_dec_ref(v_a_2517_);
    lean_dec(v_a_2516_);
    lean_dec_ref(v_a_2515_);
    lean_dec(v_a_2514_);
    lean_dec_ref(v_a_2513_);
    return v_res_2522_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1()
-> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2532_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5;
    v___x_2533_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2;
    v___x_2534_ = lean_alloc_closure(
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
    mut v_a_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2537_: *mut LeanObject = core::ptr::null_mut();
    v_res_2537_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
    return v_res_2537_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3()
-> *mut LeanObject {
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    v___x_2564_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2;
    v___x_2565_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6;
    v___x_2566_ = l_Lean_addBuiltinDeclarationRanges(v___x_2564_, v___x_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(
    mut v_a_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2568_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
    return v_res_2568_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint =
        _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint,
    );
    res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Split(builtin);
}
