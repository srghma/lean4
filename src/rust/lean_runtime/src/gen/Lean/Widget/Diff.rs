// Lean compiler output
// Module: Lean.Widget.Diff
// Imports: Lean.Widget.InteractiveGoal
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_zip___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringString___lam__0___boxed;
use crate::r#gen::Init::Data::ToString::Extra::l_List_toString___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getForallBinderNames,
    l_Lean_Expr_getForallBodyMaxDepth, l_Lean_Expr_hasMVar, l_Lean_Expr_mvar___override,
    l_Lean_Expr_sort___override, l_Lean_MVarIdSet_ofArray, l_Lean_instBEqBinderInfo_beq,
    l_Lean_instBEqMVarId_beq,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_contains, l_Lean_LocalContext_findFromUserName_x3f,
    l_Lean_LocalContext_sanitizeNames, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_getFVarFromUserName,
    l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findDecl_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::SubExpr::{
    l_Lean_SubExpr_Pos_pushBindingBody, l_Lean_SubExpr_Pos_pushBindingDomain,
    l_Lean_SubExpr_Pos_pushNaryArg, l_Lean_SubExpr_Pos_pushNthBindingBody,
    l_Lean_SubExpr_Pos_pushNthBindingDomain, l_Lean_SubExpr_Pos_pushProj, l_Lean_SubExpr_Pos_root,
    l_Lean_SubExpr_Pos_toString,
};
use crate::r#gen::Lean::Widget::InteractiveCode::l_Lean_Widget_SubexprInfo_withDiffTag;
use crate::r#gen::Lean::Widget::InteractiveGoal::{
    initialize_Lean_Widget_InteractiveGoal, runtime_initialize_Lean_Widget_InteractiveGoal,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_Const_alter___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_foldl___redArg, l_Std_DTreeMap_Internal_Impl_foldrM___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{
    lean_expr_eqv, lean_expr_instantiate_rev, lean_expr_instantiate1,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 104, 111, 119, 84, 97, 99, 116, 105, 99, 68, 105, 102, 102, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6622324566003052713 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<86> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [87, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 105, 110, 116, 101, 114, 97, 99, 116, 105, 118, 101, 32, 103, 111, 97, 108, 115, 32, 102, 111, 114, 32, 116, 97, 99, 116, 105, 99, 115, 32, 119, 105, 108, 108, 32, 98, 101, 32, 100, 101, 99, 111, 114, 97, 116, 101, 100, 32, 119, 105, 116, 104, 32, 100, 105, 102, 102, 105, 110, 103, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 46, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4735983161311130606 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [68, 105, 102, 102, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7775793824594353132 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6645386215732740461 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10488261404848132824 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9842793936046282308 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13397182889434623170 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 104, 97, 110, 103, 101, 0],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 101, 108, 101, 116, 101, 0],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 115, 101, 114, 116, 0],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 101, 102, 111, 114, 101, 58, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [10, 97, 102, 116, 101, 114, 58, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 104, 97, 112, 112, 101, 110, 0,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 101, 109, 112, 116, 121, 32, 102, 118, 97, 114, 32, 108, 105, 115, 116, 33, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value:
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
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        85, 110, 107, 110, 111, 119, 110, 32, 103, 111, 97, 108, 32, 0,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 100, 101, 99, 108,
        32, 102, 111, 114, 32, 0,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value:
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
    m_data: [46, 0],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 103, 111, 97, 108, 32, 0]};
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(
    mut v_name_2858_: *mut crate::leanh::LeanObject,
    mut v_decl_2859_: *mut crate::leanh::LeanObject,
    mut v_ref_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2862_ = crate::leanh::lean_ctor_get(v_decl_2859_, 0);
                v_descr_2863_ = crate::leanh::lean_ctor_get(v_decl_2859_, 1);
                v_deprecation_x3f_2864_ = crate::leanh::lean_ctor_get(v_decl_2859_, 2);
                v___x_2865_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2866_ = (crate::leanh::lean_unbox(v_defValue_2862_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_2865_, 0 as u32, v___x_2866_);
                crate::leanh::lean_inc(v_deprecation_x3f_2864_);
                crate::leanh::lean_inc_ref(v_descr_2863_);
                crate::leanh::lean_inc_n(v_name_2858_, 2);
                v___x_2867_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2867_, 0, v_name_2858_);
                crate::leanh::lean_ctor_set(v___x_2867_, 1, v_ref_2860_);
                crate::leanh::lean_ctor_set(v___x_2867_, 2, v___x_2865_);
                crate::leanh::lean_ctor_set(v___x_2867_, 3, v_descr_2863_);
                crate::leanh::lean_ctor_set(v___x_2867_, 4, v_deprecation_x3f_2864_);
                v___x_2868_ = lean_register_option(v_name_2858_, v___x_2867_);
                if crate::leanh::lean_obj_tag(v___x_2868_) == 0 {
                    v_isSharedCheck_2876_ = (!crate::leanh::lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2876_ == 0 {
                        v_unused_2877_ = crate::leanh::lean_ctor_get(v___x_2868_, 0);
                        crate::leanh::lean_dec(v_unused_2877_);
                        v___x_2870_ = v___x_2868_;
                        v_isShared_2871_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2868_);
                        v___x_2870_ = crate::leanh::lean_box(0);
                        v_isShared_2871_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2858_);
                    v_a_2878_ = crate::leanh::lean_ctor_get(v___x_2868_, 0);
                    v_isSharedCheck_2885_ = (!crate::leanh::lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2885_ == 0 {
                        v___x_2880_ = v___x_2868_;
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2878_);
                        crate::leanh::lean_dec(v___x_2868_);
                        v___x_2880_ = crate::leanh::lean_box(0);
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_2862_);
                v___x_2872_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2872_, 0, v_name_2858_);
                crate::leanh::lean_ctor_set(v___x_2872_, 1, v_defValue_2862_);
                if v_isShared_2871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2874_;
            }
            3 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2886_: *mut crate::leanh::LeanObject,
    mut v_decl_2887_: *mut crate::leanh::LeanObject,
    mut v_ref_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_2886_, v_decl_2887_, v_ref_2888_);
    crate::leanh::lean_dec_ref(v_decl_2887_);
    return v_res_2890_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2930_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2931_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2932_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_2929_, v___x_2930_, v___x_2931_);
    return v___x_2932_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(
    mut v_a_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2934_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
    return v_res_2934_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(
    mut v_x_2935_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_2935_ {
        0 => {
            let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2936_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2936_;
        }
        1 => {
            let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2937_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2937_;
        }
        _ => {
            let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2938_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2938_;
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(
    mut v_x_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2940_: u8 = 0;
    let mut v_res_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2940_ = (crate::leanh::lean_unbox(v_x_2939_) as u8);
    v_res_2941_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_boxed_2940_);
    return v_res_2941_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(
    mut v_x_2942_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2943_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_2942_);
    return v___x_2943_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(
    mut v_x_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_2945_: u8 = 0;
    let mut v_res_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2945_ = (crate::leanh::lean_unbox(v_x_2944_) as u8);
    v_res_2946_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(v_x_4__boxed_2945_);
    return v_res_2946_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(
    mut v_k_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2947_);
    return v_k_2947_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(
    mut v_k_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_2948_);
    crate::leanh::lean_dec(v_k_2948_);
    return v_res_2949_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(
    mut v_motive_2950_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2951_: *mut crate::leanh::LeanObject,
    mut v_t_2952_: u8,
    mut v_h_2953_: *mut crate::leanh::LeanObject,
    mut v_k_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_2954_);
    return v_k_2954_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(
    mut v_motive_2955_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2956_: *mut crate::leanh::LeanObject,
    mut v_t_2957_: *mut crate::leanh::LeanObject,
    mut v_h_2958_: *mut crate::leanh::LeanObject,
    mut v_k_2959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2960_: u8 = 0;
    let mut v_res_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2960_ = (crate::leanh::lean_unbox(v_t_2957_) as u8);
    v_res_2961_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(
        v_motive_2955_,
        v_ctorIdx_2956_,
        v_t_boxed_2960_,
        v_h_2958_,
        v_k_2959_,
    );
    crate::leanh::lean_dec(v_k_2959_);
    crate::leanh::lean_dec(v_ctorIdx_2956_);
    return v_res_2961_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(
    mut v_change_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_change_2962_);
    return v_change_2962_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(
    mut v_change_2963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2964_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(
        v_change_2963_,
    );
    crate::leanh::lean_dec(v_change_2963_);
    return v_res_2964_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(
    mut v_motive_2965_: *mut crate::leanh::LeanObject,
    mut v_t_2966_: u8,
    mut v_h_2967_: *mut crate::leanh::LeanObject,
    mut v_change_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_change_2968_);
    return v_change_2968_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(
    mut v_motive_2969_: *mut crate::leanh::LeanObject,
    mut v_t_2970_: *mut crate::leanh::LeanObject,
    mut v_h_2971_: *mut crate::leanh::LeanObject,
    mut v_change_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2973_: u8 = 0;
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2973_ = (crate::leanh::lean_unbox(v_t_2970_) as u8);
    v_res_2974_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(
        v_motive_2969_,
        v_t_boxed_2973_,
        v_h_2971_,
        v_change_2972_,
    );
    crate::leanh::lean_dec(v_change_2972_);
    return v_res_2974_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(
    mut v_delete_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_delete_2975_);
    return v_delete_2975_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(
    mut v_delete_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(
        v_delete_2976_,
    );
    crate::leanh::lean_dec(v_delete_2976_);
    return v_res_2977_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(
    mut v_motive_2978_: *mut crate::leanh::LeanObject,
    mut v_t_2979_: u8,
    mut v_h_2980_: *mut crate::leanh::LeanObject,
    mut v_delete_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_delete_2981_);
    return v_delete_2981_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(
    mut v_motive_2982_: *mut crate::leanh::LeanObject,
    mut v_t_2983_: *mut crate::leanh::LeanObject,
    mut v_h_2984_: *mut crate::leanh::LeanObject,
    mut v_delete_2985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2986_: u8 = 0;
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2986_ = (crate::leanh::lean_unbox(v_t_2983_) as u8);
    v_res_2987_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(
        v_motive_2982_,
        v_t_boxed_2986_,
        v_h_2984_,
        v_delete_2985_,
    );
    crate::leanh::lean_dec(v_delete_2985_);
    return v_res_2987_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(
    mut v_insert_2988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_insert_2988_);
    return v_insert_2988_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(
    mut v_insert_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2990_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(
        v_insert_2989_,
    );
    crate::leanh::lean_dec(v_insert_2989_);
    return v_res_2990_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(
    mut v_motive_2991_: *mut crate::leanh::LeanObject,
    mut v_t_2992_: u8,
    mut v_h_2993_: *mut crate::leanh::LeanObject,
    mut v_insert_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_insert_2994_);
    return v_insert_2994_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(
    mut v_motive_2995_: *mut crate::leanh::LeanObject,
    mut v_t_2996_: *mut crate::leanh::LeanObject,
    mut v_h_2997_: *mut crate::leanh::LeanObject,
    mut v_insert_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_2999_: u8 = 0;
    let mut v_res_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2999_ = (crate::leanh::lean_unbox(v_t_2996_) as u8);
    v_res_3000_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(
        v_motive_2995_,
        v_t_boxed_2999_,
        v_h_2997_,
        v_insert_2998_,
    );
    crate::leanh::lean_dec(v_insert_2998_);
    return v_res_3000_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(
    mut v_x_3001_: u8,
    mut v_x_3002_: u8,
) -> u8 {
    if v_x_3001_ == 0 {
        match v_x_3002_ {
            0 => {
                let mut v___x_3003_: u8 = 0;
                v___x_3003_ = 1;
                return v___x_3003_;
            }
            1 => {
                let mut v___x_3004_: u8 = 0;
                v___x_3004_ = 3;
                return v___x_3004_;
            }
            _ => {
                let mut v___x_3005_: u8 = 0;
                v___x_3005_ = 5;
                return v___x_3005_;
            }
        }
    } else {
        match v_x_3002_ {
            0 => {
                let mut v___x_3006_: u8 = 0;
                v___x_3006_ = 0;
                return v___x_3006_;
            }
            1 => {
                let mut v___x_3007_: u8 = 0;
                v___x_3007_ = 2;
                return v___x_3007_;
            }
            _ => {
                let mut v___x_3008_: u8 = 0;
                v___x_3008_ = 4;
                return v___x_3008_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag___boxed(
    mut v_x_3009_: *mut crate::leanh::LeanObject,
    mut v_x_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_49__boxed_3011_: u8 = 0;
    let mut v_x_50__boxed_3012_: u8 = 0;
    let mut v_res_3013_: u8 = 0;
    let mut v_r_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_49__boxed_3011_ = (crate::leanh::lean_unbox(v_x_3009_) as u8);
    v_x_50__boxed_3012_ = (crate::leanh::lean_unbox(v_x_3010_) as u8);
    v_res_3013_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(
        v_x_49__boxed_3011_,
        v_x_50__boxed_3012_,
    );
    v_r_3014_ = crate::leanh::lean_box((v_res_3013_) as usize);
    return v_r_3014_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(
    mut v_x_3018_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_3018_ {
        0 => {
            let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3019_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0;
            return v___x_3019_;
        }
        1 => {
            let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3020_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1;
            return v___x_3020_;
        }
        _ => {
            let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3021_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2;
            return v___x_3021_;
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(
    mut v_x_3022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_31__boxed_3023_: u8 = 0;
    let mut v_res_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_31__boxed_3023_ = (crate::leanh::lean_unbox(v_x_3022_) as u8);
    v_res_3024_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_3023_);
    return v_res_3024_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(
    mut v_x_3030_: *mut crate::leanh::LeanObject,
    mut v_y_3031_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3032_: u8 = 0;
    v___x_3032_ = lean_nat_dec_lt(v_x_3030_, v_y_3031_);
    if v___x_3032_ == 0 {
        let mut v___x_3033_: u8 = 0;
        v___x_3033_ = lean_nat_dec_eq(v_x_3030_, v_y_3031_);
        if v___x_3033_ == 0 {
            let mut v___x_3034_: u8 = 0;
            v___x_3034_ = 2;
            return v___x_3034_;
        } else {
            let mut v___x_3035_: u8 = 0;
            v___x_3035_ = 1;
            return v___x_3035_;
        }
    } else {
        let mut v___x_3036_: u8 = 0;
        v___x_3036_ = 0;
        return v___x_3036_;
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0___boxed(
    mut v_x_3037_: *mut crate::leanh::LeanObject,
    mut v_y_3038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3039_: u8 = 0;
    let mut v_r_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3039_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(
        v_x_3037_, v_y_3038_,
    );
    crate::leanh::lean_dec(v_y_3038_);
    crate::leanh::lean_dec(v_x_3037_);
    v_r_3040_ = crate::leanh::lean_box((v_res_3039_) as usize);
    return v_r_3040_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(
    mut v_b_u2082_3041_: u8,
    mut v_x_3042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = crate::leanh::lean_box((v_b_u2082_3041_) as usize);
    v___x_3044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(
    mut v_b_u2082_3045_: *mut crate::leanh::LeanObject,
    mut v_x_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_u2082_boxed_3047_: u8 = 0;
    let mut v_res_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3047_ = (crate::leanh::lean_unbox(v_b_u2082_3045_) as u8);
    v_res_3048_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(
        v_b_u2082_boxed_3047_,
        v_x_3046_,
    );
    crate::leanh::lean_dec(v_x_3046_);
    return v_res_3048_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(
    mut v___f_3049_: *mut crate::leanh::LeanObject,
    mut v_t_3050_: *mut crate::leanh::LeanObject,
    mut v_a_3051_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_3052_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3053_ = crate::leanh::lean_box((v_b_u2082_3052_) as usize);
    v___f_3054_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3054_, 0, v___x_3053_);
    v___x_3055_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v___f_3049_,
        v_a_3051_,
        v___f_3054_,
        v_t_3050_,
    );
    return v___x_3055_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(
    mut v___f_3056_: *mut crate::leanh::LeanObject,
    mut v_t_3057_: *mut crate::leanh::LeanObject,
    mut v_a_3058_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_u2082_boxed_3060_: u8 = 0;
    let mut v_res_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3060_ = (crate::leanh::lean_unbox(v_b_u2082_3059_) as u8);
    v_res_3061_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(
        v___f_3056_,
        v_t_3057_,
        v_a_3058_,
        v_b_u2082_boxed_3060_,
    );
    return v_res_3061_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(
    mut v___f_3062_: *mut crate::leanh::LeanObject,
    mut v___f_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_b_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_changesBefore_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3066_ = crate::leanh::lean_ctor_get(v_a_3064_, 0);
                crate::leanh::lean_inc(v_changesBefore_3066_);
                v_changesAfter_3067_ = crate::leanh::lean_ctor_get(v_a_3064_, 1);
                crate::leanh::lean_inc(v_changesAfter_3067_);
                crate::leanh::lean_dec_ref(v_a_3064_);
                v_changesBefore_3068_ = crate::leanh::lean_ctor_get(v_b_3065_, 0);
                v_changesAfter_3069_ = crate::leanh::lean_ctor_get(v_b_3065_, 1);
                v_isSharedCheck_3078_ = (!crate::leanh::lean_is_exclusive(v_b_3065_)) as u8;
                if v_isSharedCheck_3078_ == 0 {
                    v___x_3071_ = v_b_3065_;
                    v_isShared_3072_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_changesAfter_3069_);
                    crate::leanh::lean_inc(v_changesBefore_3068_);
                    crate::leanh::lean_dec(v_b_3065_);
                    v___x_3071_ = crate::leanh::lean_box(0);
                    v_isShared_3072_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3073_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3062_,
                    v_changesBefore_3066_,
                    v_changesBefore_3068_,
                );
                v___x_3074_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_3063_,
                    v_changesAfter_3067_,
                    v_changesAfter_3069_,
                );
                if v_isShared_3072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3071_, 1, v___x_3074_);
                    crate::leanh::lean_ctor_set(v___x_3071_, 0, v___x_3073_);
                    v___x_3076_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3074_);
                    v___x_3076_ = v_reuseFailAlloc_3077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(
    mut v_x_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3089_ = crate::leanh::lean_ctor_get(v_x_3088_, 0);
    v_snd_3090_ = crate::leanh::lean_ctor_get(v_x_3088_, 1);
    v___x_3091_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0;
    v___x_3092_ = l_Lean_SubExpr_Pos_toString(v_fst_3089_);
    v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
    crate::leanh::lean_dec_ref(v___x_3092_);
    v___x_3094_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1;
    v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
    v___x_3096_ = (crate::leanh::lean_unbox(v_snd_3090_) as u8);
    v___x_3097_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_3096_);
    v___x_3098_ = lean_string_append(v___x_3095_, v___x_3097_);
    crate::leanh::lean_dec_ref(v___x_3097_);
    v___x_3099_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2;
    v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
    return v___x_3100_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(
    mut v_x_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3102_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_3101_);
    crate::leanh::lean_dec_ref(v_x_3101_);
    return v_res_3102_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(
    mut v_x1_3103_: *mut crate::leanh::LeanObject,
    mut v_x2_3104_: u8,
    mut v_x3_3105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = crate::leanh::lean_box((v_x2_3104_) as usize);
    v___x_3107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3107_, 0, v_x1_3103_);
    crate::leanh::lean_ctor_set(v___x_3107_, 1, v___x_3106_);
    v___x_3108_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3108_, 0, v___x_3107_);
    crate::leanh::lean_ctor_set(v___x_3108_, 1, v_x3_3105_);
    return v___x_3108_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(
    mut v_x1_3109_: *mut crate::leanh::LeanObject,
    mut v_x2_3110_: *mut crate::leanh::LeanObject,
    mut v_x3_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_243__boxed_3112_: u8 = 0;
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_243__boxed_3112_ = (crate::leanh::lean_unbox(v_x2_3110_) as u8);
    v_res_3113_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(
        v_x1_3109_,
        v_x2_243__boxed_3112_,
        v_x3_3111_,
    );
    return v_res_3113_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(
    mut v___f_3133_: *mut crate::leanh::LeanObject,
    mut v___f_3134_: *mut crate::leanh::LeanObject,
    mut v_p_3135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3136_ = crate::leanh::lean_box(0);
    v___x_3137_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9;
    v___x_3138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(
        v___x_3137_,
        v___f_3133_,
        v___x_3136_,
        v_p_3135_,
    );
    v___x_3139_ = l_List_mapTR_loop___redArg(v___f_3134_, v___x_3138_, v___x_3136_);
    return v___x_3139_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3(
    mut v_f_3142_: *mut crate::leanh::LeanObject,
    mut v___f_3143_: *mut crate::leanh::LeanObject,
    mut v_x_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_changesBefore_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_changesBefore_3145_ = crate::leanh::lean_ctor_get(v_x_3144_, 0);
    crate::leanh::lean_inc(v_changesBefore_3145_);
    v_changesAfter_3146_ = crate::leanh::lean_ctor_get(v_x_3144_, 1);
    crate::leanh::lean_inc(v_changesAfter_3146_);
    crate::leanh::lean_dec_ref(v_x_3144_);
    v___x_3147_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0;
    crate::leanh::lean_inc_ref(v_f_3142_);
    v___x_3148_ = crate::leanh::lean_apply_1(v_f_3142_, v_changesBefore_3145_);
    crate::leanh::lean_inc_ref(v___f_3143_);
    v___x_3149_ = l_List_toString___redArg(v___f_3143_, v___x_3148_);
    v___x_3150_ = lean_string_append(v___x_3147_, v___x_3149_);
    crate::leanh::lean_dec_ref(v___x_3149_);
    v___x_3151_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1;
    v___x_3152_ = lean_string_append(v___x_3150_, v___x_3151_);
    v___x_3153_ = crate::leanh::lean_apply_1(v_f_3142_, v_changesAfter_3146_);
    v___x_3154_ = l_List_toString___redArg(v___f_3143_, v___x_3153_);
    v___x_3155_ = lean_string_append(v___x_3152_, v___x_3154_);
    crate::leanh::lean_dec_ref(v___x_3154_);
    return v___x_3155_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(
    mut v_k_3166_: *mut crate::leanh::LeanObject,
    mut v_v_3167_: *mut crate::leanh::LeanObject,
    mut v_t_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: u8 = 0;
    let mut v_impl_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v_size_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_unused_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_unused_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut v_unused_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v_k_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_unused_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_unused_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: u8 = 0;
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3335_: u8 = 0;
    let mut v_size_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v_unused_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v_unused_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_unused_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut v_unused_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_k_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_unused_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_unused_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3168_) == 0 {
                    v_size_3169_ = crate::leanh::lean_ctor_get(v_t_3168_, 0);
                    v_k_3170_ = crate::leanh::lean_ctor_get(v_t_3168_, 1);
                    v_v_3171_ = crate::leanh::lean_ctor_get(v_t_3168_, 2);
                    v_l_3172_ = crate::leanh::lean_ctor_get(v_t_3168_, 3);
                    v_r_3173_ = crate::leanh::lean_ctor_get(v_t_3168_, 4);
                    v_isSharedCheck_3454_ = (!crate::leanh::lean_is_exclusive(v_t_3168_)) as u8;
                    if v_isSharedCheck_3454_ == 0 {
                        v___x_3175_ = v_t_3168_;
                        v_isShared_3176_ = v_isSharedCheck_3454_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3173_);
                        crate::leanh::lean_inc(v_l_3172_);
                        crate::leanh::lean_inc(v_v_3171_);
                        crate::leanh::lean_inc(v_k_3170_);
                        crate::leanh::lean_inc(v_size_3169_);
                        crate::leanh::lean_dec(v_t_3168_);
                        v___x_3175_ = crate::leanh::lean_box(0);
                        v_isShared_3176_ = v_isSharedCheck_3454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3455_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3456_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3455_);
                    crate::leanh::lean_ctor_set(v___x_3456_, 1, v_k_3166_);
                    crate::leanh::lean_ctor_set(v___x_3456_, 2, v_v_3167_);
                    crate::leanh::lean_ctor_set(v___x_3456_, 3, v_t_3168_);
                    crate::leanh::lean_ctor_set(v___x_3456_, 4, v_t_3168_);
                    return v___x_3456_;
                }
            }
            1 => {
                v___x_3177_ = lean_nat_dec_lt(v_k_3166_, v_k_3170_);
                if v___x_3177_ == 0 {
                    v___x_3178_ = lean_nat_dec_eq(v_k_3166_, v_k_3170_);
                    if v___x_3178_ == 0 {
                        crate::leanh::lean_dec(v_size_3169_);
                        v_impl_3179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3166_, v_v_3167_, v_r_3173_);
                        v___x_3180_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_3172_) == 0 {
                            v_size_3181_ = crate::leanh::lean_ctor_get(v_l_3172_, 0);
                            v_size_3182_ = crate::leanh::lean_ctor_get(v_impl_3179_, 0);
                            crate::leanh::lean_inc(v_size_3182_);
                            v_k_3183_ = crate::leanh::lean_ctor_get(v_impl_3179_, 1);
                            crate::leanh::lean_inc(v_k_3183_);
                            v_v_3184_ = crate::leanh::lean_ctor_get(v_impl_3179_, 2);
                            crate::leanh::lean_inc(v_v_3184_);
                            v_l_3185_ = crate::leanh::lean_ctor_get(v_impl_3179_, 3);
                            crate::leanh::lean_inc(v_l_3185_);
                            v_r_3186_ = crate::leanh::lean_ctor_get(v_impl_3179_, 4);
                            crate::leanh::lean_inc(v_r_3186_);
                            v___x_3187_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3188_ = lean_nat_mul(v___x_3187_, v_size_3181_);
                            v___x_3189_ = lean_nat_dec_lt(v___x_3188_, v_size_3182_);
                            crate::leanh::lean_dec(v___x_3188_);
                            if v___x_3189_ == 0 {
                                crate::leanh::lean_dec(v_r_3186_);
                                crate::leanh::lean_dec(v_l_3185_);
                                crate::leanh::lean_dec(v_v_3184_);
                                crate::leanh::lean_dec(v_k_3183_);
                                v___x_3190_ = lean_nat_add(v___x_3180_, v_size_3181_);
                                v___x_3191_ = lean_nat_add(v___x_3190_, v_size_3182_);
                                crate::leanh::lean_dec(v_size_3182_);
                                crate::leanh::lean_dec(v___x_3190_);
                                if v_isShared_3176_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v_impl_3179_);
                                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3191_);
                                    v___x_3193_ = v___x_3175_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3194_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3194_,
                                        0,
                                        v___x_3191_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3194_,
                                        1,
                                        v_k_3170_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3194_,
                                        2,
                                        v_v_3171_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3194_,
                                        3,
                                        v_l_3172_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3194_,
                                        4,
                                        v_impl_3179_,
                                    );
                                    v___x_3193_ = v_reuseFailAlloc_3194_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3258_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3179_)) as u8;
                                if v_isSharedCheck_3258_ == 0 {
                                    v_unused_3259_ = crate::leanh::lean_ctor_get(v_impl_3179_, 4);
                                    crate::leanh::lean_dec(v_unused_3259_);
                                    v_unused_3260_ = crate::leanh::lean_ctor_get(v_impl_3179_, 3);
                                    crate::leanh::lean_dec(v_unused_3260_);
                                    v_unused_3261_ = crate::leanh::lean_ctor_get(v_impl_3179_, 2);
                                    crate::leanh::lean_dec(v_unused_3261_);
                                    v_unused_3262_ = crate::leanh::lean_ctor_get(v_impl_3179_, 1);
                                    crate::leanh::lean_dec(v_unused_3262_);
                                    v_unused_3263_ = crate::leanh::lean_ctor_get(v_impl_3179_, 0);
                                    crate::leanh::lean_dec(v_unused_3263_);
                                    v___x_3196_ = v_impl_3179_;
                                    v_isShared_3197_ = v_isSharedCheck_3258_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_3179_);
                                    v___x_3196_ = crate::leanh::lean_box(0);
                                    v_isShared_3197_ = v_isSharedCheck_3258_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3264_ = crate::leanh::lean_ctor_get(v_impl_3179_, 3);
                            crate::leanh::lean_inc(v_l_3264_);
                            if crate::leanh::lean_obj_tag(v_l_3264_) == 0 {
                                v_r_3265_ = crate::leanh::lean_ctor_get(v_impl_3179_, 4);
                                v_k_3266_ = crate::leanh::lean_ctor_get(v_impl_3179_, 1);
                                v_v_3267_ = crate::leanh::lean_ctor_get(v_impl_3179_, 2);
                                v_isSharedCheck_3290_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3179_)) as u8;
                                if v_isSharedCheck_3290_ == 0 {
                                    v_unused_3291_ = crate::leanh::lean_ctor_get(v_impl_3179_, 3);
                                    crate::leanh::lean_dec(v_unused_3291_);
                                    v_unused_3292_ = crate::leanh::lean_ctor_get(v_impl_3179_, 0);
                                    crate::leanh::lean_dec(v_unused_3292_);
                                    v___x_3269_ = v_impl_3179_;
                                    v_isShared_3270_ = v_isSharedCheck_3290_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3265_);
                                    crate::leanh::lean_inc(v_v_3267_);
                                    crate::leanh::lean_inc(v_k_3266_);
                                    crate::leanh::lean_dec(v_impl_3179_);
                                    v___x_3269_ = crate::leanh::lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3290_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3293_ = crate::leanh::lean_ctor_get(v_impl_3179_, 4);
                                crate::leanh::lean_inc(v_r_3293_);
                                if crate::leanh::lean_obj_tag(v_r_3293_) == 0 {
                                    v_k_3294_ = crate::leanh::lean_ctor_get(v_impl_3179_, 1);
                                    v_v_3295_ = crate::leanh::lean_ctor_get(v_impl_3179_, 2);
                                    v_isSharedCheck_3306_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_3179_)) as u8;
                                    if v_isSharedCheck_3306_ == 0 {
                                        v_unused_3307_ =
                                            crate::leanh::lean_ctor_get(v_impl_3179_, 4);
                                        crate::leanh::lean_dec(v_unused_3307_);
                                        v_unused_3308_ =
                                            crate::leanh::lean_ctor_get(v_impl_3179_, 3);
                                        crate::leanh::lean_dec(v_unused_3308_);
                                        v_unused_3309_ =
                                            crate::leanh::lean_ctor_get(v_impl_3179_, 0);
                                        crate::leanh::lean_dec(v_unused_3309_);
                                        v___x_3297_ = v_impl_3179_;
                                        v_isShared_3298_ = v_isSharedCheck_3306_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3295_);
                                        crate::leanh::lean_inc(v_k_3294_);
                                        crate::leanh::lean_dec(v_impl_3179_);
                                        v___x_3297_ = crate::leanh::lean_box(0);
                                        v_isShared_3298_ = v_isSharedCheck_3306_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_3310_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_3176_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3175_, 4, v_impl_3179_);
                                        crate::leanh::lean_ctor_set(v___x_3175_, 3, v_r_3293_);
                                        crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3310_);
                                        v___x_3312_ = v___x_3175_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3313_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3313_,
                                            0,
                                            v___x_3310_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3313_,
                                            1,
                                            v_k_3170_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3313_,
                                            2,
                                            v_v_3171_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3313_,
                                            3,
                                            v_r_3293_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3313_,
                                            4,
                                            v_impl_3179_,
                                        );
                                        v___x_3312_ = v_reuseFailAlloc_3313_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_3171_);
                        crate::leanh::lean_dec(v_k_3170_);
                        if v_isShared_3176_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3167_);
                            crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3166_);
                            v___x_3315_ = v___x_3175_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3316_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_size_3169_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_k_3166_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_v_3167_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 3, v_l_3172_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 4, v_r_3173_);
                            v___x_3315_ = v_reuseFailAlloc_3316_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_3169_);
                    v_impl_3317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3166_, v_v_3167_, v_l_3172_);
                    v___x_3318_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_3173_) == 0 {
                        v_size_3319_ = crate::leanh::lean_ctor_get(v_r_3173_, 0);
                        v_size_3320_ = crate::leanh::lean_ctor_get(v_impl_3317_, 0);
                        crate::leanh::lean_inc(v_size_3320_);
                        v_k_3321_ = crate::leanh::lean_ctor_get(v_impl_3317_, 1);
                        crate::leanh::lean_inc(v_k_3321_);
                        v_v_3322_ = crate::leanh::lean_ctor_get(v_impl_3317_, 2);
                        crate::leanh::lean_inc(v_v_3322_);
                        v_l_3323_ = crate::leanh::lean_ctor_get(v_impl_3317_, 3);
                        crate::leanh::lean_inc(v_l_3323_);
                        v_r_3324_ = crate::leanh::lean_ctor_get(v_impl_3317_, 4);
                        crate::leanh::lean_inc(v_r_3324_);
                        v___x_3325_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_3326_ = lean_nat_mul(v___x_3325_, v_size_3319_);
                        v___x_3327_ = lean_nat_dec_lt(v___x_3326_, v_size_3320_);
                        crate::leanh::lean_dec(v___x_3326_);
                        if v___x_3327_ == 0 {
                            crate::leanh::lean_dec(v_r_3324_);
                            crate::leanh::lean_dec(v_l_3323_);
                            crate::leanh::lean_dec(v_v_3322_);
                            crate::leanh::lean_dec(v_k_3321_);
                            v___x_3328_ = lean_nat_add(v___x_3318_, v_size_3320_);
                            crate::leanh::lean_dec(v_size_3320_);
                            v___x_3329_ = lean_nat_add(v___x_3328_, v_size_3319_);
                            crate::leanh::lean_dec(v___x_3328_);
                            if v_isShared_3176_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3175_, 3, v_impl_3317_);
                                crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3329_);
                                v___x_3331_ = v___x_3175_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3332_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_k_3170_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_v_3171_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3332_,
                                    3,
                                    v_impl_3317_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 4, v_r_3173_);
                                v___x_3331_ = v_reuseFailAlloc_3332_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3398_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_3317_)) as u8;
                            if v_isSharedCheck_3398_ == 0 {
                                v_unused_3399_ = crate::leanh::lean_ctor_get(v_impl_3317_, 4);
                                crate::leanh::lean_dec(v_unused_3399_);
                                v_unused_3400_ = crate::leanh::lean_ctor_get(v_impl_3317_, 3);
                                crate::leanh::lean_dec(v_unused_3400_);
                                v_unused_3401_ = crate::leanh::lean_ctor_get(v_impl_3317_, 2);
                                crate::leanh::lean_dec(v_unused_3401_);
                                v_unused_3402_ = crate::leanh::lean_ctor_get(v_impl_3317_, 1);
                                crate::leanh::lean_dec(v_unused_3402_);
                                v_unused_3403_ = crate::leanh::lean_ctor_get(v_impl_3317_, 0);
                                crate::leanh::lean_dec(v_unused_3403_);
                                v___x_3334_ = v_impl_3317_;
                                v_isShared_3335_ = v_isSharedCheck_3398_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_3317_);
                                v___x_3334_ = crate::leanh::lean_box(0);
                                v_isShared_3335_ = v_isSharedCheck_3398_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3404_ = crate::leanh::lean_ctor_get(v_impl_3317_, 3);
                        crate::leanh::lean_inc(v_l_3404_);
                        if crate::leanh::lean_obj_tag(v_l_3404_) == 0 {
                            v_r_3405_ = crate::leanh::lean_ctor_get(v_impl_3317_, 4);
                            v_k_3406_ = crate::leanh::lean_ctor_get(v_impl_3317_, 1);
                            v_v_3407_ = crate::leanh::lean_ctor_get(v_impl_3317_, 2);
                            v_isSharedCheck_3418_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_3317_)) as u8;
                            if v_isSharedCheck_3418_ == 0 {
                                v_unused_3419_ = crate::leanh::lean_ctor_get(v_impl_3317_, 3);
                                crate::leanh::lean_dec(v_unused_3419_);
                                v_unused_3420_ = crate::leanh::lean_ctor_get(v_impl_3317_, 0);
                                crate::leanh::lean_dec(v_unused_3420_);
                                v___x_3409_ = v_impl_3317_;
                                v_isShared_3410_ = v_isSharedCheck_3418_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_3405_);
                                crate::leanh::lean_inc(v_v_3407_);
                                crate::leanh::lean_inc(v_k_3406_);
                                crate::leanh::lean_dec(v_impl_3317_);
                                v___x_3409_ = crate::leanh::lean_box(0);
                                v_isShared_3410_ = v_isSharedCheck_3418_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3421_ = crate::leanh::lean_ctor_get(v_impl_3317_, 4);
                            crate::leanh::lean_inc(v_r_3421_);
                            if crate::leanh::lean_obj_tag(v_r_3421_) == 0 {
                                v_k_3422_ = crate::leanh::lean_ctor_get(v_impl_3317_, 1);
                                v_v_3423_ = crate::leanh::lean_ctor_get(v_impl_3317_, 2);
                                v_isSharedCheck_3446_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_3317_)) as u8;
                                if v_isSharedCheck_3446_ == 0 {
                                    v_unused_3447_ = crate::leanh::lean_ctor_get(v_impl_3317_, 4);
                                    crate::leanh::lean_dec(v_unused_3447_);
                                    v_unused_3448_ = crate::leanh::lean_ctor_get(v_impl_3317_, 3);
                                    crate::leanh::lean_dec(v_unused_3448_);
                                    v_unused_3449_ = crate::leanh::lean_ctor_get(v_impl_3317_, 0);
                                    crate::leanh::lean_dec(v_unused_3449_);
                                    v___x_3425_ = v_impl_3317_;
                                    v_isShared_3426_ = v_isSharedCheck_3446_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_3423_);
                                    crate::leanh::lean_inc(v_k_3422_);
                                    crate::leanh::lean_dec(v_impl_3317_);
                                    v___x_3425_ = crate::leanh::lean_box(0);
                                    v_isShared_3426_ = v_isSharedCheck_3446_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3450_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_3176_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v_r_3421_);
                                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v_impl_3317_);
                                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3450_);
                                    v___x_3452_ = v___x_3175_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3453_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3453_,
                                        0,
                                        v___x_3450_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3453_,
                                        1,
                                        v_k_3170_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3453_,
                                        2,
                                        v_v_3171_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3453_,
                                        3,
                                        v_impl_3317_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3453_,
                                        4,
                                        v_r_3421_,
                                    );
                                    v___x_3452_ = v_reuseFailAlloc_3453_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3193_;
            }
            3 => {
                v_size_3198_ = crate::leanh::lean_ctor_get(v_l_3185_, 0);
                v_k_3199_ = crate::leanh::lean_ctor_get(v_l_3185_, 1);
                v_v_3200_ = crate::leanh::lean_ctor_get(v_l_3185_, 2);
                v_l_3201_ = crate::leanh::lean_ctor_get(v_l_3185_, 3);
                v_r_3202_ = crate::leanh::lean_ctor_get(v_l_3185_, 4);
                v_size_3203_ = crate::leanh::lean_ctor_get(v_r_3186_, 0);
                v___x_3204_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3205_ = lean_nat_mul(v___x_3204_, v_size_3203_);
                v___x_3206_ = lean_nat_dec_lt(v_size_3198_, v___x_3205_);
                crate::leanh::lean_dec(v___x_3205_);
                if v___x_3206_ == 0 {
                    crate::leanh::lean_inc(v_r_3202_);
                    crate::leanh::lean_inc(v_l_3201_);
                    crate::leanh::lean_inc(v_v_3200_);
                    crate::leanh::lean_inc(v_k_3199_);
                    v_isSharedCheck_3234_ = (!crate::leanh::lean_is_exclusive(v_l_3185_)) as u8;
                    if v_isSharedCheck_3234_ == 0 {
                        v_unused_3235_ = crate::leanh::lean_ctor_get(v_l_3185_, 4);
                        crate::leanh::lean_dec(v_unused_3235_);
                        v_unused_3236_ = crate::leanh::lean_ctor_get(v_l_3185_, 3);
                        crate::leanh::lean_dec(v_unused_3236_);
                        v_unused_3237_ = crate::leanh::lean_ctor_get(v_l_3185_, 2);
                        crate::leanh::lean_dec(v_unused_3237_);
                        v_unused_3238_ = crate::leanh::lean_ctor_get(v_l_3185_, 1);
                        crate::leanh::lean_dec(v_unused_3238_);
                        v_unused_3239_ = crate::leanh::lean_ctor_get(v_l_3185_, 0);
                        crate::leanh::lean_dec(v_unused_3239_);
                        v___x_3208_ = v_l_3185_;
                        v_isShared_3209_ = v_isSharedCheck_3234_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3185_);
                        v___x_3208_ = crate::leanh::lean_box(0);
                        v_isShared_3209_ = v_isSharedCheck_3234_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3175_);
                    v___x_3240_ = lean_nat_add(v___x_3180_, v_size_3181_);
                    v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3182_);
                    crate::leanh::lean_dec(v_size_3182_);
                    v___x_3242_ = lean_nat_add(v___x_3240_, v_size_3198_);
                    crate::leanh::lean_dec(v___x_3240_);
                    crate::leanh::lean_inc_ref(v_l_3172_);
                    if v_isShared_3197_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3196_, 4, v_l_3185_);
                        crate::leanh::lean_ctor_set(v___x_3196_, 3, v_l_3172_);
                        crate::leanh::lean_ctor_set(v___x_3196_, 2, v_v_3171_);
                        crate::leanh::lean_ctor_set(v___x_3196_, 1, v_k_3170_);
                        crate::leanh::lean_ctor_set(v___x_3196_, 0, v___x_3242_);
                        v___x_3244_ = v___x_3196_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3257_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3242_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_k_3170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_v_3171_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_l_3172_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_l_3185_);
                        v___x_3244_ = v_reuseFailAlloc_3257_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3210_ = lean_nat_add(v___x_3180_, v_size_3181_);
                v___x_3211_ = lean_nat_add(v___x_3210_, v_size_3182_);
                crate::leanh::lean_dec(v_size_3182_);
                if crate::leanh::lean_obj_tag(v_l_3201_) == 0 {
                    v_size_3232_ = crate::leanh::lean_ctor_get(v_l_3201_, 0);
                    crate::leanh::lean_inc(v_size_3232_);
                    v___y_3224_ = v_size_3232_;
                    state = 8;
                    continue;
                } else {
                    v___x_3233_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3224_ = v___x_3233_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3216_ = lean_nat_add(v___y_3213_, v___y_3215_);
                crate::leanh::lean_dec(v___y_3215_);
                crate::leanh::lean_dec(v___y_3213_);
                if v_isShared_3209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3208_, 4, v_r_3186_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 3, v_r_3202_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 2, v_v_3184_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 1, v_k_3183_);
                    crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3216_);
                    v___x_3218_ = v___x_3208_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_k_3183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 2, v_v_3184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 3, v_r_3202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 4, v_r_3186_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3196_, 4, v___x_3218_);
                    crate::leanh::lean_ctor_set(v___x_3196_, 3, v___y_3214_);
                    crate::leanh::lean_ctor_set(v___x_3196_, 2, v_v_3200_);
                    crate::leanh::lean_ctor_set(v___x_3196_, 1, v_k_3199_);
                    crate::leanh::lean_ctor_set(v___x_3196_, 0, v___x_3211_);
                    v___x_3220_ = v___x_3196_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 3, v___y_3214_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 4, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3220_;
            }
            8 => {
                v___x_3225_ = lean_nat_add(v___x_3210_, v___y_3224_);
                crate::leanh::lean_dec(v___y_3224_);
                crate::leanh::lean_dec(v___x_3210_);
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v_l_3201_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3225_);
                    v___x_3227_ = v___x_3175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_l_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_l_3201_);
                    v___x_3227_ = v_reuseFailAlloc_3231_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3228_ = lean_nat_add(v___x_3180_, v_size_3203_);
                if crate::leanh::lean_obj_tag(v_r_3202_) == 0 {
                    v_size_3229_ = crate::leanh::lean_ctor_get(v_r_3202_, 0);
                    crate::leanh::lean_inc(v_size_3229_);
                    v___y_3213_ = v___x_3228_;
                    v___y_3214_ = v___x_3227_;
                    v___y_3215_ = v_size_3229_;
                    state = 5;
                    continue;
                } else {
                    v___x_3230_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3213_ = v___x_3228_;
                    v___y_3214_ = v___x_3227_;
                    v___y_3215_ = v___x_3230_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3251_ = (!crate::leanh::lean_is_exclusive(v_l_3172_)) as u8;
                if v_isSharedCheck_3251_ == 0 {
                    v_unused_3252_ = crate::leanh::lean_ctor_get(v_l_3172_, 4);
                    crate::leanh::lean_dec(v_unused_3252_);
                    v_unused_3253_ = crate::leanh::lean_ctor_get(v_l_3172_, 3);
                    crate::leanh::lean_dec(v_unused_3253_);
                    v_unused_3254_ = crate::leanh::lean_ctor_get(v_l_3172_, 2);
                    crate::leanh::lean_dec(v_unused_3254_);
                    v_unused_3255_ = crate::leanh::lean_ctor_get(v_l_3172_, 1);
                    crate::leanh::lean_dec(v_unused_3255_);
                    v_unused_3256_ = crate::leanh::lean_ctor_get(v_l_3172_, 0);
                    crate::leanh::lean_dec(v_unused_3256_);
                    v___x_3246_ = v_l_3172_;
                    v_isShared_3247_ = v_isSharedCheck_3251_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_3172_);
                    v___x_3246_ = crate::leanh::lean_box(0);
                    v_isShared_3247_ = v_isSharedCheck_3251_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3246_, 4, v_r_3186_);
                    crate::leanh::lean_ctor_set(v___x_3246_, 3, v___x_3244_);
                    crate::leanh::lean_ctor_set(v___x_3246_, 2, v_v_3184_);
                    crate::leanh::lean_ctor_set(v___x_3246_, 1, v_k_3183_);
                    crate::leanh::lean_ctor_set(v___x_3246_, 0, v___x_3241_);
                    v___x_3249_ = v___x_3246_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3250_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_k_3183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 2, v_v_3184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 3, v___x_3244_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3250_, 4, v_r_3186_);
                    v___x_3249_ = v_reuseFailAlloc_3250_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3249_;
            }
            13 => {
                v_k_3271_ = crate::leanh::lean_ctor_get(v_l_3264_, 1);
                v_v_3272_ = crate::leanh::lean_ctor_get(v_l_3264_, 2);
                v_isSharedCheck_3286_ = (!crate::leanh::lean_is_exclusive(v_l_3264_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v_unused_3287_ = crate::leanh::lean_ctor_get(v_l_3264_, 4);
                    crate::leanh::lean_dec(v_unused_3287_);
                    v_unused_3288_ = crate::leanh::lean_ctor_get(v_l_3264_, 3);
                    crate::leanh::lean_dec(v_unused_3288_);
                    v_unused_3289_ = crate::leanh::lean_ctor_get(v_l_3264_, 0);
                    crate::leanh::lean_dec(v_unused_3289_);
                    v___x_3274_ = v_l_3264_;
                    v_isShared_3275_ = v_isSharedCheck_3286_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3272_);
                    crate::leanh::lean_inc(v_k_3271_);
                    crate::leanh::lean_dec(v_l_3264_);
                    v___x_3274_ = crate::leanh::lean_box(0);
                    v_isShared_3275_ = v_isSharedCheck_3286_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3276_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_3265_, 2);
                if v_isShared_3275_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3274_, 4, v_r_3265_);
                    crate::leanh::lean_ctor_set(v___x_3274_, 3, v_r_3265_);
                    crate::leanh::lean_ctor_set(v___x_3274_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v___x_3274_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v___x_3274_, 0, v___x_3180_);
                    v___x_3278_ = v___x_3274_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 3, v_r_3265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 4, v_r_3265_);
                    v___x_3278_ = v_reuseFailAlloc_3285_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_3265_);
                if v_isShared_3270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3269_, 3, v_r_3265_);
                    crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3180_);
                    v___x_3280_ = v___x_3269_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3266_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_r_3265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_r_3265_);
                    v___x_3280_ = v_reuseFailAlloc_3284_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v___x_3280_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v___x_3278_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3272_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3271_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3276_);
                    v___x_3282_ = v___x_3175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_k_3271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 2, v_v_3272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 3, v___x_3278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3283_, 4, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3282_;
            }
            18 => {
                v___x_3299_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3298_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3297_, 4, v_l_3264_);
                    crate::leanh::lean_ctor_set(v___x_3297_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v___x_3297_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v___x_3297_, 0, v___x_3180_);
                    v___x_3301_ = v___x_3297_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3305_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_l_3264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_l_3264_);
                    v___x_3301_ = v_reuseFailAlloc_3305_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v_r_3293_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v___x_3301_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3295_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3294_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3299_);
                    v___x_3303_ = v___x_3175_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_k_3294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_v_3295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 3, v___x_3301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_r_3293_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3303_;
            }
            21 => {
                return v___x_3312_;
            }
            22 => {
                return v___x_3315_;
            }
            23 => {
                return v___x_3331_;
            }
            24 => {
                v_size_3336_ = crate::leanh::lean_ctor_get(v_l_3323_, 0);
                v_size_3337_ = crate::leanh::lean_ctor_get(v_r_3324_, 0);
                v_k_3338_ = crate::leanh::lean_ctor_get(v_r_3324_, 1);
                v_v_3339_ = crate::leanh::lean_ctor_get(v_r_3324_, 2);
                v_l_3340_ = crate::leanh::lean_ctor_get(v_r_3324_, 3);
                v_r_3341_ = crate::leanh::lean_ctor_get(v_r_3324_, 4);
                v___x_3342_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3343_ = lean_nat_mul(v___x_3342_, v_size_3336_);
                v___x_3344_ = lean_nat_dec_lt(v_size_3337_, v___x_3343_);
                crate::leanh::lean_dec(v___x_3343_);
                if v___x_3344_ == 0 {
                    crate::leanh::lean_inc(v_r_3341_);
                    crate::leanh::lean_inc(v_l_3340_);
                    crate::leanh::lean_inc(v_v_3339_);
                    crate::leanh::lean_inc(v_k_3338_);
                    v_isSharedCheck_3373_ = (!crate::leanh::lean_is_exclusive(v_r_3324_)) as u8;
                    if v_isSharedCheck_3373_ == 0 {
                        v_unused_3374_ = crate::leanh::lean_ctor_get(v_r_3324_, 4);
                        crate::leanh::lean_dec(v_unused_3374_);
                        v_unused_3375_ = crate::leanh::lean_ctor_get(v_r_3324_, 3);
                        crate::leanh::lean_dec(v_unused_3375_);
                        v_unused_3376_ = crate::leanh::lean_ctor_get(v_r_3324_, 2);
                        crate::leanh::lean_dec(v_unused_3376_);
                        v_unused_3377_ = crate::leanh::lean_ctor_get(v_r_3324_, 1);
                        crate::leanh::lean_dec(v_unused_3377_);
                        v_unused_3378_ = crate::leanh::lean_ctor_get(v_r_3324_, 0);
                        crate::leanh::lean_dec(v_unused_3378_);
                        v___x_3346_ = v_r_3324_;
                        v_isShared_3347_ = v_isSharedCheck_3373_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3324_);
                        v___x_3346_ = crate::leanh::lean_box(0);
                        v_isShared_3347_ = v_isSharedCheck_3373_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3175_);
                    v___x_3379_ = lean_nat_add(v___x_3318_, v_size_3320_);
                    crate::leanh::lean_dec(v_size_3320_);
                    v___x_3380_ = lean_nat_add(v___x_3379_, v_size_3319_);
                    crate::leanh::lean_dec(v___x_3379_);
                    v___x_3381_ = lean_nat_add(v___x_3318_, v_size_3319_);
                    v___x_3382_ = lean_nat_add(v___x_3381_, v_size_3337_);
                    crate::leanh::lean_dec(v___x_3381_);
                    crate::leanh::lean_inc_ref(v_r_3173_);
                    if v_isShared_3335_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3334_, 4, v_r_3173_);
                        crate::leanh::lean_ctor_set(v___x_3334_, 3, v_r_3324_);
                        crate::leanh::lean_ctor_set(v___x_3334_, 2, v_v_3171_);
                        crate::leanh::lean_ctor_set(v___x_3334_, 1, v_k_3170_);
                        crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3382_);
                        v___x_3384_ = v___x_3334_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3397_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3382_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3170_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3171_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 3, v_r_3324_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3397_, 4, v_r_3173_);
                        v___x_3384_ = v_reuseFailAlloc_3397_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3348_ = lean_nat_add(v___x_3318_, v_size_3320_);
                crate::leanh::lean_dec(v_size_3320_);
                v___x_3349_ = lean_nat_add(v___x_3348_, v_size_3319_);
                crate::leanh::lean_dec(v___x_3348_);
                v___x_3361_ = lean_nat_add(v___x_3318_, v_size_3336_);
                if crate::leanh::lean_obj_tag(v_l_3340_) == 0 {
                    v_size_3371_ = crate::leanh::lean_ctor_get(v_l_3340_, 0);
                    crate::leanh::lean_inc(v_size_3371_);
                    v___y_3363_ = v_size_3371_;
                    state = 29;
                    continue;
                } else {
                    v___x_3372_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3363_ = v___x_3372_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3354_ = lean_nat_add(v___y_3352_, v___y_3353_);
                crate::leanh::lean_dec(v___y_3353_);
                crate::leanh::lean_dec(v___y_3352_);
                if v_isShared_3347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3346_, 4, v_r_3173_);
                    crate::leanh::lean_ctor_set(v___x_3346_, 3, v_r_3341_);
                    crate::leanh::lean_ctor_set(v___x_3346_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v___x_3346_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3354_);
                    v___x_3356_ = v___x_3346_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 3, v_r_3341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 4, v_r_3173_);
                    v___x_3356_ = v_reuseFailAlloc_3360_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3334_, 4, v___x_3356_);
                    crate::leanh::lean_ctor_set(v___x_3334_, 3, v___y_3351_);
                    crate::leanh::lean_ctor_set(v___x_3334_, 2, v_v_3339_);
                    crate::leanh::lean_ctor_set(v___x_3334_, 1, v_k_3338_);
                    crate::leanh::lean_ctor_set(v___x_3334_, 0, v___x_3349_);
                    v___x_3358_ = v___x_3334_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_k_3338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 2, v_v_3339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 3, v___y_3351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 4, v___x_3356_);
                    v___x_3358_ = v_reuseFailAlloc_3359_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3358_;
            }
            29 => {
                v___x_3364_ = lean_nat_add(v___x_3361_, v___y_3363_);
                crate::leanh::lean_dec(v___y_3363_);
                crate::leanh::lean_dec(v___x_3361_);
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v_l_3340_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v_l_3323_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3322_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3321_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3364_);
                    v___x_3366_ = v___x_3175_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3340_);
                    v___x_3366_ = v_reuseFailAlloc_3370_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3367_ = lean_nat_add(v___x_3318_, v_size_3319_);
                if crate::leanh::lean_obj_tag(v_r_3341_) == 0 {
                    v_size_3368_ = crate::leanh::lean_ctor_get(v_r_3341_, 0);
                    crate::leanh::lean_inc(v_size_3368_);
                    v___y_3351_ = v___x_3366_;
                    v___y_3352_ = v___x_3367_;
                    v___y_3353_ = v_size_3368_;
                    state = 26;
                    continue;
                } else {
                    v___x_3369_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3351_ = v___x_3366_;
                    v___y_3352_ = v___x_3367_;
                    v___y_3353_ = v___x_3369_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3391_ = (!crate::leanh::lean_is_exclusive(v_r_3173_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v_unused_3392_ = crate::leanh::lean_ctor_get(v_r_3173_, 4);
                    crate::leanh::lean_dec(v_unused_3392_);
                    v_unused_3393_ = crate::leanh::lean_ctor_get(v_r_3173_, 3);
                    crate::leanh::lean_dec(v_unused_3393_);
                    v_unused_3394_ = crate::leanh::lean_ctor_get(v_r_3173_, 2);
                    crate::leanh::lean_dec(v_unused_3394_);
                    v_unused_3395_ = crate::leanh::lean_ctor_get(v_r_3173_, 1);
                    crate::leanh::lean_dec(v_unused_3395_);
                    v_unused_3396_ = crate::leanh::lean_ctor_get(v_r_3173_, 0);
                    crate::leanh::lean_dec(v_unused_3396_);
                    v___x_3386_ = v_r_3173_;
                    v_isShared_3387_ = v_isSharedCheck_3391_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_3173_);
                    v___x_3386_ = crate::leanh::lean_box(0);
                    v_isShared_3387_ = v_isSharedCheck_3391_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3387_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3386_, 4, v___x_3384_);
                    crate::leanh::lean_ctor_set(v___x_3386_, 3, v_l_3323_);
                    crate::leanh::lean_ctor_set(v___x_3386_, 2, v_v_3322_);
                    crate::leanh::lean_ctor_set(v___x_3386_, 1, v_k_3321_);
                    crate::leanh::lean_ctor_set(v___x_3386_, 0, v___x_3380_);
                    v___x_3389_ = v___x_3386_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_k_3321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_v_3322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_l_3323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 4, v___x_3384_);
                    v___x_3389_ = v_reuseFailAlloc_3390_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3389_;
            }
            34 => {
                v___x_3411_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_3405_);
                if v_isShared_3410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3409_, 3, v_r_3405_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 0, v___x_3318_);
                    v___x_3413_ = v___x_3409_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_r_3405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_r_3405_);
                    v___x_3413_ = v_reuseFailAlloc_3417_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v___x_3413_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v_l_3404_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3407_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3406_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3411_);
                    v___x_3415_ = v___x_3175_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3416_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_k_3406_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_v_3407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_l_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3416_, 4, v___x_3413_);
                    v___x_3415_ = v_reuseFailAlloc_3416_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3415_;
            }
            37 => {
                v_k_3427_ = crate::leanh::lean_ctor_get(v_r_3421_, 1);
                v_v_3428_ = crate::leanh::lean_ctor_get(v_r_3421_, 2);
                v_isSharedCheck_3442_ = (!crate::leanh::lean_is_exclusive(v_r_3421_)) as u8;
                if v_isSharedCheck_3442_ == 0 {
                    v_unused_3443_ = crate::leanh::lean_ctor_get(v_r_3421_, 4);
                    crate::leanh::lean_dec(v_unused_3443_);
                    v_unused_3444_ = crate::leanh::lean_ctor_get(v_r_3421_, 3);
                    crate::leanh::lean_dec(v_unused_3444_);
                    v_unused_3445_ = crate::leanh::lean_ctor_get(v_r_3421_, 0);
                    crate::leanh::lean_dec(v_unused_3445_);
                    v___x_3430_ = v_r_3421_;
                    v_isShared_3431_ = v_isSharedCheck_3442_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3428_);
                    crate::leanh::lean_inc(v_k_3427_);
                    crate::leanh::lean_dec(v_r_3421_);
                    v___x_3430_ = crate::leanh::lean_box(0);
                    v_isShared_3431_ = v_isSharedCheck_3442_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3432_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3430_, 4, v_l_3404_);
                    crate::leanh::lean_ctor_set(v___x_3430_, 3, v_l_3404_);
                    crate::leanh::lean_ctor_set(v___x_3430_, 2, v_v_3423_);
                    crate::leanh::lean_ctor_set(v___x_3430_, 1, v_k_3422_);
                    crate::leanh::lean_ctor_set(v___x_3430_, 0, v___x_3318_);
                    v___x_3434_ = v___x_3430_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_k_3422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_v_3423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 3, v_l_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3441_, 4, v_l_3404_);
                    v___x_3434_ = v_reuseFailAlloc_3441_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3425_, 4, v_l_3404_);
                    crate::leanh::lean_ctor_set(v___x_3425_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v___x_3425_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v___x_3425_, 0, v___x_3318_);
                    v___x_3436_ = v___x_3425_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3440_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 3, v_l_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_l_3404_);
                    v___x_3436_ = v_reuseFailAlloc_3440_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3176_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3175_, 4, v___x_3436_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 3, v___x_3434_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 2, v_v_3428_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 1, v_k_3427_);
                    crate::leanh::lean_ctor_set(v___x_3175_, 0, v___x_3432_);
                    v___x_3438_ = v___x_3175_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_k_3427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_v_3428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 3, v___x_3434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 4, v___x_3436_);
                    v___x_3438_ = v_reuseFailAlloc_3439_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3438_;
            }
            42 => {
                return v___x_3452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(
    mut v_p_3457_: *mut crate::leanh::LeanObject,
    mut v_d_3458_: u8,
    mut v_00_u03b4_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_changesBefore_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3460_ = crate::leanh::lean_ctor_get(v_00_u03b4_3459_, 0);
                v_changesAfter_3461_ = crate::leanh::lean_ctor_get(v_00_u03b4_3459_, 1);
                v_isSharedCheck_3470_ = (!crate::leanh::lean_is_exclusive(v_00_u03b4_3459_)) as u8;
                if v_isSharedCheck_3470_ == 0 {
                    v___x_3463_ = v_00_u03b4_3459_;
                    v_isShared_3464_ = v_isSharedCheck_3470_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_changesAfter_3461_);
                    crate::leanh::lean_inc(v_changesBefore_3460_);
                    crate::leanh::lean_dec(v_00_u03b4_3459_);
                    v___x_3463_ = crate::leanh::lean_box(0);
                    v_isShared_3464_ = v_isSharedCheck_3470_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3465_ = crate::leanh::lean_box((v_d_3458_) as usize);
                v___x_3466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_3457_, v___x_3465_, v_changesBefore_3460_);
                if v_isShared_3464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3463_, 0, v___x_3466_);
                    v___x_3468_ = v___x_3463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_changesAfter_3461_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange___boxed(
    mut v_p_3471_: *mut crate::leanh::LeanObject,
    mut v_d_3472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_boxed_3474_: u8 = 0;
    let mut v_res_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_d_boxed_3474_ = (crate::leanh::lean_unbox(v_d_3472_) as u8);
    v_res_3475_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(
        v_p_3471_,
        v_d_boxed_3474_,
        v_00_u03b4_3473_,
    );
    return v_res_3475_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(
    mut v_00_u03b2_3476_: *mut crate::leanh::LeanObject,
    mut v_k_3477_: *mut crate::leanh::LeanObject,
    mut v_v_3478_: *mut crate::leanh::LeanObject,
    mut v_t_3479_: *mut crate::leanh::LeanObject,
    mut v_hl_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3477_, v_v_3478_, v_t_3479_);
    return v___x_3481_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(
    mut v_p_3482_: *mut crate::leanh::LeanObject,
    mut v_d_3483_: u8,
    mut v_00_u03b4_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_changesBefore_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3485_ = crate::leanh::lean_ctor_get(v_00_u03b4_3484_, 0);
                v_changesAfter_3486_ = crate::leanh::lean_ctor_get(v_00_u03b4_3484_, 1);
                v_isSharedCheck_3495_ = (!crate::leanh::lean_is_exclusive(v_00_u03b4_3484_)) as u8;
                if v_isSharedCheck_3495_ == 0 {
                    v___x_3488_ = v_00_u03b4_3484_;
                    v_isShared_3489_ = v_isSharedCheck_3495_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_changesAfter_3486_);
                    crate::leanh::lean_inc(v_changesBefore_3485_);
                    crate::leanh::lean_dec(v_00_u03b4_3484_);
                    v___x_3488_ = crate::leanh::lean_box(0);
                    v_isShared_3489_ = v_isSharedCheck_3495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3490_ = crate::leanh::lean_box((v_d_3483_) as usize);
                v___x_3491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_3482_, v___x_3490_, v_changesAfter_3486_);
                if v_isShared_3489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3488_, 1, v___x_3491_);
                    v___x_3493_ = v___x_3488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_changesBefore_3485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange___boxed(
    mut v_p_3496_: *mut crate::leanh::LeanObject,
    mut v_d_3497_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_d_boxed_3499_ = (crate::leanh::lean_unbox(v_d_3497_) as u8);
    v_res_3500_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(
        v_p_3496_,
        v_d_boxed_3499_,
        v_00_u03b4_3498_,
    );
    return v_res_3500_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
    mut v_before_3501_: *mut crate::leanh::LeanObject,
    mut v_after_3502_: *mut crate::leanh::LeanObject,
    mut v_d_3503_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = crate::leanh::lean_box(1);
    v___x_3505_ = crate::leanh::lean_box((v_d_3503_) as usize);
    v___x_3506_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_3501_, v___x_3505_, v___x_3504_);
    v___x_3507_ = crate::leanh::lean_box((v_d_3503_) as usize);
    v___x_3508_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_3502_, v___x_3507_, v___x_3504_);
    v___x_3509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3506_);
    crate::leanh::lean_ctor_set(v___x_3509_, 1, v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(
    mut v_before_3510_: *mut crate::leanh::LeanObject,
    mut v_after_3511_: *mut crate::leanh::LeanObject,
    mut v_d_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_boxed_3513_: u8 = 0;
    let mut v_res_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_d_boxed_3513_ = (crate::leanh::lean_unbox(v_d_3512_) as u8);
    v_res_3514_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
        v_before_3510_,
        v_after_3511_,
        v_d_boxed_3513_,
    );
    return v_res_3514_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
    mut v_before_3515_: *mut crate::leanh::LeanObject,
    mut v_after_3516_: *mut crate::leanh::LeanObject,
    mut v_d_3517_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_3518_ = crate::leanh::lean_ctor_get(v_before_3515_, 1);
    crate::leanh::lean_inc(v_pos_3518_);
    crate::leanh::lean_dec_ref(v_before_3515_);
    v_pos_3519_ = crate::leanh::lean_ctor_get(v_after_3516_, 1);
    crate::leanh::lean_inc(v_pos_3519_);
    crate::leanh::lean_dec_ref(v_after_3516_);
    v___x_3520_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
        v_pos_3518_,
        v_pos_3519_,
        v_d_3517_,
    );
    return v___x_3520_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(
    mut v_before_3521_: *mut crate::leanh::LeanObject,
    mut v_after_3522_: *mut crate::leanh::LeanObject,
    mut v_d_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_boxed_3524_: u8 = 0;
    let mut v_res_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_d_boxed_3524_ = (crate::leanh::lean_unbox(v_d_3523_) as u8);
    v_res_3525_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
        v_before_3521_,
        v_after_3522_,
        v_d_boxed_3524_,
    );
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(
    mut v_d_3526_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_changesAfter_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_changesAfter_3527_ = crate::leanh::lean_ctor_get(v_d_3526_, 1);
    if crate::leanh::lean_obj_tag(v_changesAfter_3527_) == 0 {
        let mut v___x_3528_: u8 = 0;
        v___x_3528_ = 0;
        return v___x_3528_;
    } else {
        let mut v_changesBefore_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_changesBefore_3529_ = crate::leanh::lean_ctor_get(v_d_3526_, 0);
        if crate::leanh::lean_obj_tag(v_changesBefore_3529_) == 0 {
            let mut v___x_3530_: u8 = 0;
            v___x_3530_ = 0;
            return v___x_3530_;
        } else {
            let mut v___x_3531_: u8 = 0;
            v___x_3531_ = 1;
            return v___x_3531_;
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty___boxed(
    mut v_d_3532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3533_: u8 = 0;
    let mut v_r_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3533_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_3532_);
    crate::leanh::lean_dec_ref(v_d_3532_);
    v_r_3534_ = crate::leanh::lean_box((v_res_3533_) as usize);
    return v_r_3534_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(
    mut v_k_3535_: *mut crate::leanh::LeanObject,
    mut v_b_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3540_);
    crate::leanh::lean_inc_ref(v___y_3539_);
    crate::leanh::lean_inc(v___y_3538_);
    crate::leanh::lean_inc_ref(v___y_3537_);
    v___x_3542_ = crate::leanh::lean_apply_6(
        v_k_3535_,
        v_b_3536_,
        v___y_3537_,
        v___y_3538_,
        v___y_3539_,
        v___y_3540_,
        crate::leanh::lean_box(0),
    );
    return v___x_3542_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(
    mut v_k_3543_: *mut crate::leanh::LeanObject,
    mut v_b_3544_: *mut crate::leanh::LeanObject,
    mut v___y_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_3543_, v_b_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
    crate::leanh::lean_dec(v___y_3548_);
    crate::leanh::lean_dec_ref(v___y_3547_);
    crate::leanh::lean_dec(v___y_3546_);
    crate::leanh::lean_dec_ref(v___y_3545_);
    return v_res_3550_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(
    mut v_name_3551_: *mut crate::leanh::LeanObject,
    mut v_bi_3552_: u8,
    mut v_type_3553_: *mut crate::leanh::LeanObject,
    mut v_k_3554_: *mut crate::leanh::LeanObject,
    mut v_kind_3555_: u8,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_a_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3561_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_3561_, 0, v_k_3554_);
                v___x_3562_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3551_,
                    v_bi_3552_,
                    v_type_3553_,
                    v___f_3561_,
                    v_kind_3555_,
                    v___y_3556_,
                    v___y_3557_,
                    v___y_3558_,
                    v___y_3559_,
                );
                if crate::leanh::lean_obj_tag(v___x_3562_) == 0 {
                    v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3562_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3563_);
                        crate::leanh::lean_dec(v___x_3562_);
                        v___x_3565_ = crate::leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3571_ = crate::leanh::lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3578_ = (!crate::leanh::lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v___x_3573_ = v___x_3562_;
                        v_isShared_3574_ = v_isSharedCheck_3578_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3571_);
                        crate::leanh::lean_dec(v___x_3562_);
                        v___x_3573_ = crate::leanh::lean_box(0);
                        v_isShared_3574_ = v_isSharedCheck_3578_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3568_;
            }
            3 => {
                if v_isShared_3574_ == 0 {
                    v___x_3576_ = v___x_3573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
                    v___x_3576_ = v_reuseFailAlloc_3577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___boxed(
    mut v_name_3579_: *mut crate::leanh::LeanObject,
    mut v_bi_3580_: *mut crate::leanh::LeanObject,
    mut v_type_3581_: *mut crate::leanh::LeanObject,
    mut v_k_3582_: *mut crate::leanh::LeanObject,
    mut v_kind_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3589_: u8 = 0;
    let mut v_kind_boxed_3590_: u8 = 0;
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3589_ = (crate::leanh::lean_unbox(v_bi_3580_) as u8);
    v_kind_boxed_3590_ = (crate::leanh::lean_unbox(v_kind_3583_) as u8);
    v_res_3591_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_3579_, v_bi_boxed_3589_, v_type_3581_, v_k_3582_, v_kind_boxed_3590_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
    crate::leanh::lean_dec(v___y_3587_);
    crate::leanh::lean_dec_ref(v___y_3586_);
    crate::leanh::lean_dec(v___y_3585_);
    crate::leanh::lean_dec_ref(v___y_3584_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(
    mut v_00_u03b1_3592_: *mut crate::leanh::LeanObject,
    mut v_name_3593_: *mut crate::leanh::LeanObject,
    mut v_bi_3594_: u8,
    mut v_type_3595_: *mut crate::leanh::LeanObject,
    mut v_k_3596_: *mut crate::leanh::LeanObject,
    mut v_kind_3597_: u8,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
    mut v___y_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
    mut v___y_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_3593_, v_bi_3594_, v_type_3595_, v_k_3596_, v_kind_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(
    mut v_00_u03b1_3604_: *mut crate::leanh::LeanObject,
    mut v_name_3605_: *mut crate::leanh::LeanObject,
    mut v_bi_3606_: *mut crate::leanh::LeanObject,
    mut v_type_3607_: *mut crate::leanh::LeanObject,
    mut v_k_3608_: *mut crate::leanh::LeanObject,
    mut v_kind_3609_: *mut crate::leanh::LeanObject,
    mut v___y_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
    mut v___y_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3615_: u8 = 0;
    let mut v_kind_boxed_3616_: u8 = 0;
    let mut v_res_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3615_ = (crate::leanh::lean_unbox(v_bi_3606_) as u8);
    v_kind_boxed_3616_ = (crate::leanh::lean_unbox(v_kind_3609_) as u8);
    v_res_3617_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_3604_, v_name_3605_, v_bi_boxed_3615_, v_type_3607_, v_k_3608_, v_kind_boxed_3616_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
    crate::leanh::lean_dec(v___y_3613_);
    crate::leanh::lean_dec_ref(v___y_3612_);
    crate::leanh::lean_dec(v___y_3611_);
    crate::leanh::lean_dec_ref(v___y_3610_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(
    mut v_msgData_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3624_ = lean_st_ref_get(v___y_3622_);
    v_env_3625_ = crate::leanh::lean_ctor_get(v___x_3624_, 0);
    crate::leanh::lean_inc_ref(v_env_3625_);
    crate::leanh::lean_dec(v___x_3624_);
    v___x_3626_ = lean_st_ref_get(v___y_3620_);
    v_mctx_3627_ = crate::leanh::lean_ctor_get(v___x_3626_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3627_);
    crate::leanh::lean_dec(v___x_3626_);
    v_lctx_3628_ = crate::leanh::lean_ctor_get(v___y_3619_, 2);
    v_options_3629_ = crate::leanh::lean_ctor_get(v___y_3621_, 2);
    crate::leanh::lean_inc_ref(v_options_3629_);
    crate::leanh::lean_inc_ref(v_lctx_3628_);
    v___x_3630_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3630_, 0, v_env_3625_);
    crate::leanh::lean_ctor_set(v___x_3630_, 1, v_mctx_3627_);
    crate::leanh::lean_ctor_set(v___x_3630_, 2, v_lctx_3628_);
    crate::leanh::lean_ctor_set(v___x_3630_, 3, v_options_3629_);
    v___x_3631_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3631_, 0, v___x_3630_);
    crate::leanh::lean_ctor_set(v___x_3631_, 1, v_msgData_3618_);
    v___x_3632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3632_, 0, v___x_3631_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(
    mut v_msgData_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
    mut v___y_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
    crate::leanh::lean_dec(v___y_3637_);
    crate::leanh::lean_dec_ref(v___y_3636_);
    crate::leanh::lean_dec(v___y_3635_);
    crate::leanh::lean_dec_ref(v___y_3634_);
    return v_res_3639_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(
    mut v_msg_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3646_ = crate::leanh::lean_ctor_get(v___y_3643_, 5);
                v___x_3647_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
                v_a_3648_ = crate::leanh::lean_ctor_get(v___x_3647_, 0);
                v_isSharedCheck_3656_ = (!crate::leanh::lean_is_exclusive(v___x_3647_)) as u8;
                if v_isSharedCheck_3656_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    v_isShared_3651_ = v_isSharedCheck_3656_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3648_);
                    crate::leanh::lean_dec(v___x_3647_);
                    v___x_3650_ = crate::leanh::lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3646_);
                v___x_3652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3652_, 0, v_ref_3646_);
                crate::leanh::lean_ctor_set(v___x_3652_, 1, v_a_3648_);
                if v_isShared_3651_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3650_, 1);
                    crate::leanh::lean_ctor_set(v___x_3650_, 0, v___x_3652_);
                    v___x_3654_ = v___x_3650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
                    v___x_3654_ = v_reuseFailAlloc_3655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg___boxed(
    mut v_msg_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
    mut v___y_3661_: *mut crate::leanh::LeanObject,
    mut v___y_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
    crate::leanh::lean_dec(v___y_3661_);
    crate::leanh::lean_dec_ref(v___y_3660_);
    crate::leanh::lean_dec(v___y_3659_);
    crate::leanh::lean_dec_ref(v___y_3658_);
    return v_res_3663_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(
    mut v_x_3664_: *mut crate::leanh::LeanObject,
    mut v_x_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3664_) == 0 {
                    v___x_3671_ = l_List_reverse___redArg(v_x_3665_);
                    v___x_3672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                    return v___x_3672_;
                } else {
                    v_head_3673_ = crate::leanh::lean_ctor_get(v_x_3664_, 0);
                    v_tail_3674_ = crate::leanh::lean_ctor_get(v_x_3664_, 1);
                    v_isSharedCheck_3692_ = (!crate::leanh::lean_is_exclusive(v_x_3664_)) as u8;
                    if v_isSharedCheck_3692_ == 0 {
                        v___x_3676_ = v_x_3664_;
                        v_isShared_3677_ = v_isSharedCheck_3692_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3674_);
                        crate::leanh::lean_inc(v_head_3673_);
                        crate::leanh::lean_dec(v_x_3664_);
                        v___x_3676_ = crate::leanh::lean_box(0);
                        v_isShared_3677_ = v_isSharedCheck_3692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3678_ = l_Lean_Meta_getFVarFromUserName(
                    v_head_3673_,
                    v___y_3666_,
                    v___y_3667_,
                    v___y_3668_,
                    v___y_3669_,
                );
                if crate::leanh::lean_obj_tag(v___x_3678_) == 0 {
                    v_a_3679_ = crate::leanh::lean_ctor_get(v___x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3679_);
                    crate::leanh::lean_dec_ref_known(v___x_3678_, 1);
                    if v_isShared_3677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3676_, 1, v_x_3665_);
                        crate::leanh::lean_ctor_set(v___x_3676_, 0, v_a_3679_);
                        v___x_3681_ = v___x_3676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3683_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3679_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_x_3665_);
                        v___x_3681_ = v_reuseFailAlloc_3683_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3676_);
                    crate::leanh::lean_dec(v_tail_3674_);
                    crate::leanh::lean_dec(v_x_3665_);
                    v_a_3684_ = crate::leanh::lean_ctor_get(v___x_3678_, 0);
                    v_isSharedCheck_3691_ = (!crate::leanh::lean_is_exclusive(v___x_3678_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v___x_3686_ = v___x_3678_;
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3684_);
                        crate::leanh::lean_dec(v___x_3678_);
                        v___x_3686_ = crate::leanh::lean_box(0);
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_3664_ = v_tail_3674_;
                v_x_3665_ = v___x_3681_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3687_ == 0 {
                    v___x_3689_ = v___x_3686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2___boxed(
    mut v_x_3693_: *mut crate::leanh::LeanObject,
    mut v_x_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3700_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_3693_, v_x_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
    crate::leanh::lean_dec(v___y_3698_);
    crate::leanh::lean_dec_ref(v___y_3697_);
    crate::leanh::lean_dec(v___y_3696_);
    crate::leanh::lean_dec_ref(v___y_3695_);
    return v_res_3700_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(
    mut v_upperBound_3701_: *mut crate::leanh::LeanObject,
    mut v_before_3702_: *mut crate::leanh::LeanObject,
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_b_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3706_ = lean_nat_dec_lt(v_a_3703_, v_upperBound_3701_);
                if v___x_3706_ == 0 {
                    crate::leanh::lean_dec(v_a_3703_);
                    crate::leanh::lean_dec_ref(v_before_3702_);
                    v___x_3707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3707_, 0, v_b_3704_);
                    return v___x_3707_;
                } else {
                    v_pos_3708_ = crate::leanh::lean_ctor_get(v_before_3702_, 1);
                    crate::leanh::lean_inc(v_pos_3708_);
                    crate::leanh::lean_inc(v_a_3703_);
                    v___x_3709_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_3703_, v_pos_3708_);
                    v___x_3710_ = 1;
                    v___x_3711_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(
                            v___x_3709_,
                            v___x_3710_,
                            v_b_3704_,
                        );
                    v___x_3712_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3713_ = lean_nat_add(v_a_3703_, v___x_3712_);
                    crate::leanh::lean_dec(v_a_3703_);
                    v_a_3703_ = v___x_3713_;
                    v_b_3704_ = v___x_3711_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg___boxed(
    mut v_upperBound_3715_: *mut crate::leanh::LeanObject,
    mut v_before_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_b_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_3715_, v_before_3716_, v_a_3717_, v_b_3718_);
    crate::leanh::lean_dec(v_upperBound_3715_);
    return v_res_3720_;
}
pub unsafe fn l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(
    mut v_x_3721_: *mut crate::leanh::LeanObject,
    mut v_x_3722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3721_) == 0 {
                    v___x_3723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3723_, 0, v_x_3722_);
                    return v___x_3723_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3722_) == 0 {
                        v___x_3724_ = crate::leanh::lean_box(0);
                        return v___x_3724_;
                    } else {
                        v_head_3725_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
                        v_tail_3726_ = crate::leanh::lean_ctor_get(v_x_3721_, 1);
                        v_head_3727_ = crate::leanh::lean_ctor_get(v_x_3722_, 0);
                        crate::leanh::lean_inc(v_head_3727_);
                        v_tail_3728_ = crate::leanh::lean_ctor_get(v_x_3722_, 1);
                        crate::leanh::lean_inc(v_tail_3728_);
                        crate::leanh::lean_dec_ref_known(v_x_3722_, 2);
                        v___x_3729_ = lean_name_eq(v_head_3725_, v_head_3727_);
                        crate::leanh::lean_dec(v_head_3727_);
                        if v___x_3729_ == 0 {
                            crate::leanh::lean_dec(v_tail_3728_);
                            v___x_3730_ = crate::leanh::lean_box(0);
                            return v___x_3730_;
                        } else {
                            v_x_3721_ = v_tail_3726_;
                            v_x_3722_ = v_tail_3728_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0___boxed(
    mut v_x_3732_: *mut crate::leanh::LeanObject,
    mut v_x_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_3732_, v_x_3733_);
    crate::leanh::lean_dec(v_x_3732_);
    return v_res_3734_;
}
pub unsafe fn l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(
    mut v_l_u2081_3735_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = l_List_reverse___redArg(v_l_u2081_3735_);
                v___x_3738_ = l_List_reverse___redArg(v_l_u2082_3736_);
                v___x_3739_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_3737_, v___x_3738_);
                crate::leanh::lean_dec(v___x_3737_);
                if crate::leanh::lean_obj_tag(v___x_3739_) == 0 {
                    return v___x_3739_;
                } else {
                    v_val_3740_ = crate::leanh::lean_ctor_get(v___x_3739_, 0);
                    v_isSharedCheck_3748_ = (!crate::leanh::lean_is_exclusive(v___x_3739_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v___x_3742_ = v___x_3739_;
                        v_isShared_3743_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3740_);
                        crate::leanh::lean_dec(v___x_3739_);
                        v___x_3742_ = crate::leanh::lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3744_ = l_List_reverse___redArg(v_val_3740_);
                if v_isShared_3743_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3742_, 0, v___x_3744_);
                    v___x_3746_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
                    v___x_3746_ = v_reuseFailAlloc_3747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(
    mut v_b_u2082_3749_: u8,
    mut v_k_3750_: *mut crate::leanh::LeanObject,
    mut v_t_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3759_: u8 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: u8 = 0;
    let mut v_impl_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3751_) == 0 {
                    v_size_3752_ = crate::leanh::lean_ctor_get(v_t_3751_, 0);
                    v_k_3753_ = crate::leanh::lean_ctor_get(v_t_3751_, 1);
                    v_v_3754_ = crate::leanh::lean_ctor_get(v_t_3751_, 2);
                    v_l_3755_ = crate::leanh::lean_ctor_get(v_t_3751_, 3);
                    v_r_3756_ = crate::leanh::lean_ctor_get(v_t_3751_, 4);
                    v_isSharedCheck_3770_ = (!crate::leanh::lean_is_exclusive(v_t_3751_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3758_ = v_t_3751_;
                        v_isShared_3759_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3756_);
                        crate::leanh::lean_inc(v_l_3755_);
                        crate::leanh::lean_inc(v_v_3754_);
                        crate::leanh::lean_inc(v_k_3753_);
                        crate::leanh::lean_inc(v_size_3752_);
                        crate::leanh::lean_dec(v_t_3751_);
                        v___x_3758_ = crate::leanh::lean_box(0);
                        v_isShared_3759_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3771_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3772_ = crate::leanh::lean_box((v_b_u2082_3749_) as usize);
                    v___x_3773_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3773_, 0, v___x_3771_);
                    crate::leanh::lean_ctor_set(v___x_3773_, 1, v_k_3750_);
                    crate::leanh::lean_ctor_set(v___x_3773_, 2, v___x_3772_);
                    crate::leanh::lean_ctor_set(v___x_3773_, 3, v_t_3751_);
                    crate::leanh::lean_ctor_set(v___x_3773_, 4, v_t_3751_);
                    return v___x_3773_;
                }
            }
            1 => {
                v___x_3760_ = lean_nat_dec_lt(v_k_3750_, v_k_3753_);
                if v___x_3760_ == 0 {
                    v___x_3761_ = lean_nat_dec_eq(v_k_3750_, v_k_3753_);
                    if v___x_3761_ == 0 {
                        crate::leanh::lean_del_object(v___x_3758_);
                        crate::leanh::lean_dec(v_size_3752_);
                        v_impl_3762_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_3749_, v_k_3750_, v_r_3756_);
                        v___x_3763_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_3753_,
                            v_v_3754_,
                            v_l_3755_,
                            v_impl_3762_,
                        );
                        return v___x_3763_;
                    } else {
                        crate::leanh::lean_dec(v_v_3754_);
                        crate::leanh::lean_dec(v_k_3753_);
                        v___x_3764_ = crate::leanh::lean_box((v_b_u2082_3749_) as usize);
                        if v_isShared_3759_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3758_, 2, v___x_3764_);
                            crate::leanh::lean_ctor_set(v___x_3758_, 1, v_k_3750_);
                            v___x_3766_ = v___x_3758_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3767_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_size_3752_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_k_3750_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 2, v___x_3764_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 3, v_l_3755_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 4, v_r_3756_);
                            v___x_3766_ = v_reuseFailAlloc_3767_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3758_);
                    crate::leanh::lean_dec(v_size_3752_);
                    v_impl_3768_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_3749_, v_k_3750_, v_l_3755_);
                    v___x_3769_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                        v_k_3753_,
                        v_v_3754_,
                        v_impl_3768_,
                        v_r_3756_,
                    );
                    return v___x_3769_;
                }
            }
            2 => {
                return v___x_3766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg___boxed(
    mut v_b_u2082_3774_: *mut crate::leanh::LeanObject,
    mut v_k_3775_: *mut crate::leanh::LeanObject,
    mut v_t_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_u2082_boxed_3777_: u8 = 0;
    let mut v_res_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3777_ = (crate::leanh::lean_unbox(v_b_u2082_3774_) as u8);
    v_res_3778_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_3777_, v_k_3775_, v_t_3776_);
    return v_res_3778_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(
    mut v_init_3779_: *mut crate::leanh::LeanObject,
    mut v_x_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3780_) == 0 {
                    v_k_3781_ = crate::leanh::lean_ctor_get(v_x_3780_, 1);
                    crate::leanh::lean_inc(v_k_3781_);
                    v_v_3782_ = crate::leanh::lean_ctor_get(v_x_3780_, 2);
                    crate::leanh::lean_inc(v_v_3782_);
                    v_l_3783_ = crate::leanh::lean_ctor_get(v_x_3780_, 3);
                    crate::leanh::lean_inc(v_l_3783_);
                    v_r_3784_ = crate::leanh::lean_ctor_get(v_x_3780_, 4);
                    crate::leanh::lean_inc(v_r_3784_);
                    crate::leanh::lean_dec_ref_known(v_x_3780_, 5);
                    v___x_3785_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_3779_, v_l_3783_);
                    v___x_3786_ = (crate::leanh::lean_unbox(v_v_3782_) as u8);
                    crate::leanh::lean_dec(v_v_3782_);
                    v___x_3787_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v___x_3786_, v_k_3781_, v___x_3785_);
                    v_init_3779_ = v___x_3787_;
                    v_x_3780_ = v_r_3784_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3779_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(
    mut v_as_3789_: *mut crate::leanh::LeanObject,
    mut v_i_3790_: usize,
    mut v_stop_3791_: usize,
    mut v_b_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: u8 = 0;
    let mut v_changesBefore_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: usize = 0;
    let mut v___x_3807_: usize = 0;
    let mut v_reuseFailAlloc_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3793_ = lean_usize_dec_eq(v_i_3790_, v_stop_3791_);
                if v___x_3793_ == 0 {
                    v_changesBefore_3794_ = crate::leanh::lean_ctor_get(v_b_3792_, 0);
                    crate::leanh::lean_inc(v_changesBefore_3794_);
                    v_changesAfter_3795_ = crate::leanh::lean_ctor_get(v_b_3792_, 1);
                    crate::leanh::lean_inc(v_changesAfter_3795_);
                    crate::leanh::lean_dec_ref(v_b_3792_);
                    v___x_3796_ = lean_array_uget(v_as_3789_, v_i_3790_);
                    v_changesBefore_3797_ = crate::leanh::lean_ctor_get(v___x_3796_, 0);
                    v_changesAfter_3798_ = crate::leanh::lean_ctor_get(v___x_3796_, 1);
                    v_isSharedCheck_3810_ = (!crate::leanh::lean_is_exclusive(v___x_3796_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v___x_3800_ = v___x_3796_;
                        v_isShared_3801_ = v_isSharedCheck_3810_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_changesAfter_3798_);
                        crate::leanh::lean_inc(v_changesBefore_3797_);
                        crate::leanh::lean_dec(v___x_3796_);
                        v___x_3800_ = crate::leanh::lean_box(0);
                        v_isShared_3801_ = v_isSharedCheck_3810_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3792_;
                }
            }
            1 => {
                v___x_3802_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_3794_, v_changesBefore_3797_);
                v___x_3803_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_3795_, v_changesAfter_3798_);
                if v_isShared_3801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3800_, 1, v___x_3803_);
                    crate::leanh::lean_ctor_set(v___x_3800_, 0, v___x_3802_);
                    v___x_3805_ = v___x_3800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3803_);
                    v___x_3805_ = v_reuseFailAlloc_3809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3806_ = 1usize;
                v___x_3807_ = lean_usize_add(v_i_3790_, v___x_3806_);
                v_i_3790_ = v___x_3807_;
                v_b_3792_ = v___x_3805_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10___boxed(
    mut v_as_3811_: *mut crate::leanh::LeanObject,
    mut v_i_3812_: *mut crate::leanh::LeanObject,
    mut v_stop_3813_: *mut crate::leanh::LeanObject,
    mut v_b_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3815_: usize = 0;
    let mut v_stop_boxed_3816_: usize = 0;
    let mut v_res_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3815_ = crate::leanh::lean_unbox_usize(v_i_3812_);
    crate::leanh::lean_dec(v_i_3812_);
    v_stop_boxed_3816_ = crate::leanh::lean_unbox_usize(v_stop_3813_);
    crate::leanh::lean_dec(v_stop_3813_);
    v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_3811_, v_i_boxed_3815_, v_stop_boxed_3816_, v_b_3814_);
    crate::leanh::lean_dec_ref(v_as_3811_);
    return v_res_3817_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(
    mut v_x_3818_: *mut crate::leanh::LeanObject,
    mut v_x_3819_: *mut crate::leanh::LeanObject,
    mut v_x_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3818_) == 5 {
                    v_fn_3821_ = crate::leanh::lean_ctor_get(v_x_3818_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3821_);
                    v_arg_3822_ = crate::leanh::lean_ctor_get(v_x_3818_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3822_);
                    crate::leanh::lean_dec_ref_known(v_x_3818_, 2);
                    v___x_3823_ = lean_array_set(v_x_3819_, v_x_3820_, v_arg_3822_);
                    v___x_3824_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3825_ = lean_nat_sub(v_x_3820_, v___x_3824_);
                    crate::leanh::lean_dec(v_x_3820_);
                    v_x_3818_ = v_fn_3821_;
                    v_x_3819_ = v___x_3823_;
                    v_x_3820_ = v___x_3825_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_3820_);
                    v___x_3827_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3827_, 0, v_x_3818_);
                    crate::leanh::lean_ctor_set(v___x_3827_, 1, v_x_3819_);
                    return v___x_3827_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = crate::leanh::lean_box(0);
    v_dummy_3829_ = l_Lean_Expr_sort___override(v___x_3828_);
    return v_dummy_3829_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(
    mut v_snd_3830_: *mut crate::leanh::LeanObject,
    mut v_before_3831_: *mut crate::leanh::LeanObject,
    mut v_after_3832_: *mut crate::leanh::LeanObject,
    mut v_as_3833_: *mut crate::leanh::LeanObject,
    mut v_i_3834_: *mut crate::leanh::LeanObject,
    mut v_j_3835_: *mut crate::leanh::LeanObject,
    mut v_bs_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3843_: u8 = 0;
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v_pos_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3869_: u8 = 0;
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_reuseFailAlloc_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3842_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3843_ = lean_nat_dec_eq(v_i_3834_, v_zero_3842_);
                if v_isZero_3843_ == 1 {
                    crate::leanh::lean_dec(v_j_3835_);
                    crate::leanh::lean_dec(v_i_3834_);
                    v___x_3844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3844_, 0, v_bs_3836_);
                    return v___x_3844_;
                } else {
                    v___x_3845_ = lean_array_fget(v_as_3833_, v_j_3835_);
                    v_fst_3846_ = crate::leanh::lean_ctor_get(v___x_3845_, 0);
                    v_snd_3847_ = crate::leanh::lean_ctor_get(v___x_3845_, 1);
                    v_isSharedCheck_3875_ = (!crate::leanh::lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3875_ == 0 {
                        v___x_3849_ = v___x_3845_;
                        v_isShared_3850_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3847_);
                        crate::leanh::lean_inc(v_fst_3846_);
                        crate::leanh::lean_dec(v___x_3845_);
                        v___x_3849_ = crate::leanh::lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_3851_ = crate::leanh::lean_ctor_get(v_before_3831_, 1);
                v_pos_3852_ = crate::leanh::lean_ctor_get(v_after_3832_, 1);
                v___x_3853_ = lean_array_get_size(v_snd_3830_);
                v___x_3854_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_3853_, v_j_3835_, v_pos_3851_);
                if v_isShared_3850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3849_, 1, v___x_3854_);
                    v___x_3856_ = v___x_3849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_fst_3846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3854_);
                    v___x_3856_ = v_reuseFailAlloc_3874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3857_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_3853_, v_j_3835_, v_pos_3852_);
                v___x_3858_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3858_, 0, v_snd_3847_);
                crate::leanh::lean_ctor_set(v___x_3858_, 1, v___x_3857_);
                v___x_3859_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                    v___x_3856_,
                    v___x_3858_,
                    v___y_3837_,
                    v___y_3838_,
                    v___y_3839_,
                    v___y_3840_,
                );
                if crate::leanh::lean_obj_tag(v___x_3859_) == 0 {
                    v_a_3860_ = crate::leanh::lean_ctor_get(v___x_3859_, 0);
                    crate::leanh::lean_inc(v_a_3860_);
                    crate::leanh::lean_dec_ref_known(v___x_3859_, 1);
                    v_one_3861_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3862_ = lean_nat_sub(v_i_3834_, v_one_3861_);
                    crate::leanh::lean_dec(v_i_3834_);
                    v___x_3863_ = lean_nat_add(v_j_3835_, v_one_3861_);
                    crate::leanh::lean_dec(v_j_3835_);
                    v___x_3864_ = lean_array_push(v_bs_3836_, v_a_3860_);
                    v_i_3834_ = v_n_3862_;
                    v_j_3835_ = v___x_3863_;
                    v_bs_3836_ = v___x_3864_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_3836_);
                    crate::leanh::lean_dec(v_j_3835_);
                    crate::leanh::lean_dec(v_i_3834_);
                    v_a_3866_ = crate::leanh::lean_ctor_get(v___x_3859_, 0);
                    v_isSharedCheck_3873_ = (!crate::leanh::lean_is_exclusive(v___x_3859_)) as u8;
                    if v_isSharedCheck_3873_ == 0 {
                        v___x_3868_ = v___x_3859_;
                        v_isShared_3869_ = v_isSharedCheck_3873_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3866_);
                        crate::leanh::lean_dec(v___x_3859_);
                        v___x_3868_ = crate::leanh::lean_box(0);
                        v_isShared_3869_ = v_isSharedCheck_3873_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3869_ == 0 {
                    v___x_3871_ = v___x_3868_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
                    v___x_3871_ = v_reuseFailAlloc_3872_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0;
    v___x_3878_ = l_Lean_stringToMessageData(v___x_3877_);
    return v___x_3878_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(
    mut v_body_3879_: *mut crate::leanh::LeanObject,
    mut v_pos_3880_: *mut crate::leanh::LeanObject,
    mut v_body_3881_: *mut crate::leanh::LeanObject,
    mut v_pos_3882_: *mut crate::leanh::LeanObject,
    mut v_x_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(
        v_body_3879_,
        v_pos_3880_,
        v_body_3881_,
        v_pos_3882_,
        v_x_3883_,
        v___y_3884_,
        v___y_3885_,
        v___y_3886_,
        v___y_3887_,
    );
    crate::leanh::lean_dec(v___y_3887_);
    crate::leanh::lean_dec_ref(v___y_3886_);
    crate::leanh::lean_dec(v___y_3885_);
    crate::leanh::lean_dec_ref(v___y_3884_);
    crate::leanh::lean_dec_ref(v_x_3883_);
    crate::leanh::lean_dec(v_pos_3882_);
    crate::leanh::lean_dec_ref(v_body_3881_);
    crate::leanh::lean_dec(v_pos_3880_);
    crate::leanh::lean_dec_ref(v_body_3879_);
    return v_res_3889_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(
    mut v_before_3890_: *mut crate::leanh::LeanObject,
    mut v_after_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: u8 = 0;
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v___y_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: u8 = 0;
    let mut v_expr_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_u2080_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut v_a_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut v_binderName_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3977_: u8 = 0;
    let mut v_expr_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut v___x_4002_: u8 = 0;
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4008_: u8 = 0;
    let mut v___f_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4011_: u8 = 0;
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4028_: u8 = 0;
    let mut v___x_4029_: u8 = 0;
    let mut v_changesBefore_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4040_: u8 = 0;
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_reuseFailAlloc_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_unused_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_unused_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_3936_ = crate::leanh::lean_ctor_get(v_before_3890_, 0);
                v_pos_3937_ = crate::leanh::lean_ctor_get(v_before_3890_, 1);
                if crate::leanh::lean_obj_tag(v_expr_3936_) == 7 {
                    v_binderName_3974_ = crate::leanh::lean_ctor_get(v_expr_3936_, 0);
                    v_binderType_3975_ = crate::leanh::lean_ctor_get(v_expr_3936_, 1);
                    v_body_3976_ = crate::leanh::lean_ctor_get(v_expr_3936_, 2);
                    v_binderInfo_3977_ = crate::leanh::lean_ctor_get_uint8(
                        v_expr_3936_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v_expr_3978_ = crate::leanh::lean_ctor_get(v_after_3891_, 0);
                    v_pos_3979_ = crate::leanh::lean_ctor_get(v_after_3891_, 1);
                    if crate::leanh::lean_obj_tag(v_expr_3978_) == 7 {
                        v_binderName_4005_ = crate::leanh::lean_ctor_get(v_expr_3978_, 0);
                        v_binderType_4006_ = crate::leanh::lean_ctor_get(v_expr_3978_, 1);
                        v_body_4007_ = crate::leanh::lean_ctor_get(v_expr_3978_, 2);
                        v_binderInfo_4008_ = crate::leanh::lean_ctor_get_uint8(
                            v_expr_3978_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_inc(v_pos_3979_);
                        crate::leanh::lean_inc_ref(v_body_4007_);
                        crate::leanh::lean_inc(v_pos_3937_);
                        crate::leanh::lean_inc_ref(v_body_3976_);
                        v___f_4009_ = crate::leanh::lean_alloc_closure(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_4009_, 0, v_body_3976_);
                        crate::leanh::lean_closure_set(v___f_4009_, 1, v_pos_3937_);
                        crate::leanh::lean_closure_set(v___f_4009_, 2, v_body_4007_);
                        crate::leanh::lean_closure_set(v___f_4009_, 3, v_pos_3979_);
                        v___x_4061_ = lean_name_eq(v_binderName_3974_, v_binderName_4005_);
                        if v___x_4061_ == 0 {
                            v___y_4011_ = v___x_4061_;
                            state = 14;
                            continue;
                        } else {
                            v___x_4062_ = l_Lean_instBEqBinderInfo_beq(
                                v_binderInfo_3977_,
                                v_binderInfo_4008_,
                            );
                            v___y_4011_ = v___x_4062_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___y_3981_ = v_a_3892_;
                        v___y_3982_ = v_a_3893_;
                        v___y_3983_ = v_a_3894_;
                        v___y_3984_ = v_a_3895_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_after_3891_);
                    crate::leanh::lean_dec_ref(v_before_3890_);
                    v___x_4063_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                    v___x_4064_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4063_);
                    return v___x_4064_;
                }
            }
            1 => {
                v___x_3904_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_3901_, v_before_3890_, v___x_3904_, v_a_3903_);
                crate::leanh::lean_dec(v___y_3901_);
                return v___x_3905_;
            }
            2 => {
                if v___y_3914_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3909_);
                    v___x_3915_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_3910_,
                        v___y_3911_,
                        v___y_3907_,
                    );
                    crate::leanh::lean_dec_ref(v___y_3910_);
                    if crate::leanh::lean_obj_tag(v___x_3915_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3915_, 1);
                        v___x_3916_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                        v___y_3898_ = v___y_3907_;
                        v___y_3899_ = v___y_3908_;
                        v___y_3900_ = v___y_3911_;
                        v___y_3901_ = v___y_3912_;
                        v___y_3902_ = v___y_3913_;
                        v_a_3903_ = v___x_3916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_3912_);
                        crate::leanh::lean_dec_ref(v_before_3890_);
                        v_a_3917_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3924_ == 0 {
                            v___x_3919_ = v___x_3915_;
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3917_);
                            crate::leanh::lean_dec(v___x_3915_);
                            v___x_3919_ = crate::leanh::lean_box(0);
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3912_);
                    crate::leanh::lean_dec_ref(v___y_3910_);
                    crate::leanh::lean_dec_ref(v_before_3890_);
                    return v___y_3909_;
                }
            }
            3 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3922_;
            }
            5 => {
                v___x_3934_ = l_Lean_Exception_isInterrupt(v_a_3933_);
                if v___x_3934_ == 0 {
                    v___x_3935_ = l_Lean_Exception_isRuntime(v_a_3933_);
                    v___y_3907_ = v___y_3926_;
                    v___y_3908_ = v___y_3927_;
                    v___y_3909_ = v___y_3932_;
                    v___y_3910_ = v___y_3928_;
                    v___y_3911_ = v___y_3929_;
                    v___y_3912_ = v___y_3930_;
                    v___y_3913_ = v___y_3931_;
                    v___y_3914_ = v___x_3935_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_3933_);
                    v___y_3907_ = v___y_3926_;
                    v___y_3908_ = v___y_3927_;
                    v___y_3909_ = v___y_3932_;
                    v___y_3910_ = v___y_3928_;
                    v___y_3911_ = v___y_3929_;
                    v___y_3912_ = v___y_3930_;
                    v___y_3913_ = v___y_3931_;
                    v___y_3914_ = v___x_3934_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_3944_ = l_Lean_Meta_saveState___redArg(v___y_3941_, v___y_3943_);
                if crate::leanh::lean_obj_tag(v___x_3944_) == 0 {
                    v_a_3945_ = crate::leanh::lean_ctor_get(v___x_3944_, 0);
                    crate::leanh::lean_inc(v_a_3945_);
                    crate::leanh::lean_dec_ref_known(v___x_3944_, 1);
                    v___x_3946_ = l_List_lengthTR___redArg(v___y_3939_);
                    v___x_3947_ = crate::leanh::lean_box(0);
                    v___x_3948_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_3939_, v___x_3947_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
                    if crate::leanh::lean_obj_tag(v___x_3948_) == 0 {
                        v_a_3949_ = crate::leanh::lean_ctor_get(v___x_3948_, 0);
                        crate::leanh::lean_inc(v_a_3949_);
                        crate::leanh::lean_dec_ref_known(v___x_3948_, 1);
                        crate::leanh::lean_inc_n(v___x_3946_, 2);
                        v_body_u2080_3950_ =
                            l_Lean_Expr_getForallBodyMaxDepth(v___x_3946_, v_expr_3936_);
                        v___x_3951_ = lean_array_mk(v_a_3949_);
                        v___x_3952_ = lean_expr_instantiate_rev(v_body_u2080_3950_, v___x_3951_);
                        crate::leanh::lean_dec_ref(v___x_3951_);
                        crate::leanh::lean_dec_ref(v_body_u2080_3950_);
                        crate::leanh::lean_inc(v_pos_3937_);
                        v___x_3953_ =
                            l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_3946_, v_pos_3937_);
                        v___x_3954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3952_);
                        crate::leanh::lean_ctor_set(v___x_3954_, 1, v___x_3953_);
                        v___x_3955_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                            v___x_3954_,
                            v_after_3891_,
                            v___y_3940_,
                            v___y_3941_,
                            v___y_3942_,
                            v___y_3943_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3955_) == 0 {
                            crate::leanh::lean_dec(v_a_3945_);
                            v_a_3956_ = crate::leanh::lean_ctor_get(v___x_3955_, 0);
                            crate::leanh::lean_inc(v_a_3956_);
                            crate::leanh::lean_dec_ref_known(v___x_3955_, 1);
                            v___y_3898_ = v___y_3943_;
                            v___y_3899_ = v___y_3940_;
                            v___y_3900_ = v___y_3941_;
                            v___y_3901_ = v___x_3946_;
                            v___y_3902_ = v___y_3942_;
                            v_a_3903_ = v_a_3956_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3957_ = crate::leanh::lean_ctor_get(v___x_3955_, 0);
                            crate::leanh::lean_inc(v_a_3957_);
                            v___y_3926_ = v___y_3943_;
                            v___y_3927_ = v___y_3940_;
                            v___y_3928_ = v_a_3945_;
                            v___y_3929_ = v___y_3941_;
                            v___y_3930_ = v___x_3946_;
                            v___y_3931_ = v___y_3942_;
                            v___y_3932_ = v___x_3955_;
                            v_a_3933_ = v_a_3957_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_after_3891_);
                        v_a_3958_ = crate::leanh::lean_ctor_get(v___x_3948_, 0);
                        v_isSharedCheck_3965_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3948_)) as u8;
                        if v_isSharedCheck_3965_ == 0 {
                            v___x_3960_ = v___x_3948_;
                            v_isShared_3961_ = v_isSharedCheck_3965_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3958_);
                            crate::leanh::lean_dec(v___x_3948_);
                            v___x_3960_ = crate::leanh::lean_box(0);
                            v_isShared_3961_ = v_isSharedCheck_3965_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3939_);
                    crate::leanh::lean_dec_ref(v_after_3891_);
                    crate::leanh::lean_dec_ref(v_before_3890_);
                    v_a_3966_ = crate::leanh::lean_ctor_get(v___x_3944_, 0);
                    v_isSharedCheck_3973_ = (!crate::leanh::lean_is_exclusive(v___x_3944_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3968_ = v___x_3944_;
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3966_);
                        crate::leanh::lean_dec(v___x_3944_);
                        v___x_3968_ = crate::leanh::lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                crate::leanh::lean_inc(v_a_3958_);
                if v_isShared_3961_ == 0 {
                    v___x_3963_ = v___x_3960_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
                    v___x_3963_ = v_reuseFailAlloc_3964_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_3926_ = v___y_3943_;
                v___y_3927_ = v___y_3940_;
                v___y_3928_ = v_a_3945_;
                v___y_3929_ = v___y_3941_;
                v___y_3930_ = v___x_3946_;
                v___y_3931_ = v___y_3942_;
                v___y_3932_ = v___x_3963_;
                v_a_3933_ = v_a_3958_;
                state = 5;
                continue;
            }
            9 => {
                if v_isShared_3969_ == 0 {
                    v___x_3971_ = v___x_3968_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_3972_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3971_;
            }
            11 => {
                v___x_3985_ = l_Lean_Expr_getForallBinderNames(v_expr_3978_);
                v___x_3986_ = l_Lean_Expr_getForallBinderNames(v_expr_3936_);
                v___x_3987_ = l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(v___x_3985_, v___x_3986_);
                if crate::leanh::lean_obj_tag(v___x_3987_) == 1 {
                    v_val_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc(v_val_3988_);
                    crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                    v___x_3989_ = l_List_lengthTR___redArg(v_val_3988_);
                    v___x_3990_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3991_ = lean_nat_dec_eq(v___x_3989_, v___x_3990_);
                    crate::leanh::lean_dec(v___x_3989_);
                    if v___x_3991_ == 0 {
                        v___y_3939_ = v_val_3988_;
                        v___y_3940_ = v___y_3981_;
                        v___y_3941_ = v___y_3982_;
                        v___y_3942_ = v___y_3983_;
                        v___y_3943_ = v___y_3984_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3992_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
                        v___x_3993_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_3992_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
                        if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3993_, 1);
                            v___y_3939_ = v_val_3988_;
                            v___y_3940_ = v___y_3981_;
                            v___y_3941_ = v___y_3982_;
                            v___y_3942_ = v___y_3983_;
                            v___y_3943_ = v___y_3984_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_3988_);
                            crate::leanh::lean_dec_ref(v_after_3891_);
                            crate::leanh::lean_dec_ref(v_before_3890_);
                            v_a_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                            v_isSharedCheck_4001_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                            if v_isSharedCheck_4001_ == 0 {
                                v___x_3996_ = v___x_3993_;
                                v_isShared_3997_ = v_isSharedCheck_4001_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3994_);
                                crate::leanh::lean_dec(v___x_3993_);
                                v___x_3996_ = crate::leanh::lean_box(0);
                                v_isShared_3997_ = v_isSharedCheck_4001_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3987_);
                    v___x_4002_ = 0;
                    v___x_4003_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                        v_before_3890_,
                        v_after_3891_,
                        v___x_4002_,
                    );
                    v___x_4004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4004_, 0, v___x_4003_);
                    return v___x_4004_;
                }
            }
            12 => {
                if v_isShared_3997_ == 0 {
                    v___x_3999_ = v___x_3996_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4000_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
                    v___x_3999_ = v_reuseFailAlloc_4000_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3999_;
            }
            14 => {
                if v___y_4011_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_4009_);
                    v___y_3981_ = v_a_3892_;
                    v___y_3982_ = v_a_3893_;
                    v___y_3983_ = v_a_3894_;
                    v___y_3984_ = v_a_3895_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_binderType_4006_);
                    crate::leanh::lean_inc(v_pos_3979_);
                    crate::leanh::lean_inc_ref(v_binderType_3975_);
                    crate::leanh::lean_inc(v_binderName_3974_);
                    crate::leanh::lean_inc(v_pos_3937_);
                    v_isSharedCheck_4058_ =
                        (!crate::leanh::lean_is_exclusive(v_before_3890_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v_unused_4059_ = crate::leanh::lean_ctor_get(v_before_3890_, 1);
                        crate::leanh::lean_dec(v_unused_4059_);
                        v_unused_4060_ = crate::leanh::lean_ctor_get(v_before_3890_, 0);
                        crate::leanh::lean_dec(v_unused_4060_);
                        v___x_4013_ = v_before_3890_;
                        v_isShared_4014_ = v_isSharedCheck_4058_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_before_3890_);
                        v___x_4013_ = crate::leanh::lean_box(0);
                        v_isShared_4014_ = v_isSharedCheck_4058_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                v_isSharedCheck_4055_ = (!crate::leanh::lean_is_exclusive(v_after_3891_)) as u8;
                if v_isSharedCheck_4055_ == 0 {
                    v_unused_4056_ = crate::leanh::lean_ctor_get(v_after_3891_, 1);
                    crate::leanh::lean_dec(v_unused_4056_);
                    v_unused_4057_ = crate::leanh::lean_ctor_get(v_after_3891_, 0);
                    crate::leanh::lean_dec(v_unused_4057_);
                    v___x_4016_ = v_after_3891_;
                    v_isShared_4017_ = v_isSharedCheck_4055_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_after_3891_);
                    v___x_4016_ = crate::leanh::lean_box(0);
                    v_isShared_4017_ = v_isSharedCheck_4055_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4018_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_3937_);
                crate::leanh::lean_inc_ref(v_binderType_3975_);
                if v_isShared_4017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4016_, 1, v___x_4018_);
                    crate::leanh::lean_ctor_set(v___x_4016_, 0, v_binderType_3975_);
                    v___x_4020_ = v___x_4016_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_binderType_3975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4054_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4021_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_3979_);
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4021_);
                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v_binderType_4006_);
                    v___x_4023_ = v___x_4013_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_binderType_4006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4021_);
                    v___x_4023_ = v_reuseFailAlloc_4053_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4024_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                    v___x_4020_,
                    v___x_4023_,
                    v_a_3892_,
                    v_a_3893_,
                    v_a_3894_,
                    v_a_3895_,
                );
                if crate::leanh::lean_obj_tag(v___x_4024_) == 0 {
                    v_a_4025_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                    v_isSharedCheck_4052_ = (!crate::leanh::lean_is_exclusive(v___x_4024_)) as u8;
                    if v_isSharedCheck_4052_ == 0 {
                        v___x_4027_ = v___x_4024_;
                        v_isShared_4028_ = v_isSharedCheck_4052_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4025_);
                        crate::leanh::lean_dec(v___x_4024_);
                        v___x_4027_ = crate::leanh::lean_box(0);
                        v_isShared_4028_ = v_isSharedCheck_4052_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_4009_);
                    crate::leanh::lean_dec(v_pos_3979_);
                    crate::leanh::lean_dec_ref(v_binderType_3975_);
                    crate::leanh::lean_dec(v_binderName_3974_);
                    crate::leanh::lean_dec(v_pos_3937_);
                    return v___x_4024_;
                }
            }
            19 => {
                v___x_4029_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_4025_);
                if v___x_4029_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_4009_);
                    crate::leanh::lean_dec_ref(v_binderType_3975_);
                    crate::leanh::lean_dec(v_binderName_3974_);
                    v_changesBefore_4030_ = crate::leanh::lean_ctor_get(v_a_4025_, 0);
                    crate::leanh::lean_inc(v_changesBefore_4030_);
                    v_changesAfter_4031_ = crate::leanh::lean_ctor_get(v_a_4025_, 1);
                    crate::leanh::lean_inc(v_changesAfter_4031_);
                    crate::leanh::lean_dec(v_a_4025_);
                    v___x_4032_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_3937_);
                    crate::leanh::lean_dec(v_pos_3937_);
                    v___x_4033_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_3979_);
                    crate::leanh::lean_dec(v_pos_3979_);
                    v___x_4034_ = 0;
                    v___x_4035_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
                            v___x_4032_,
                            v___x_4033_,
                            v___x_4034_,
                        );
                    v_changesBefore_4036_ = crate::leanh::lean_ctor_get(v___x_4035_, 0);
                    v_changesAfter_4037_ = crate::leanh::lean_ctor_get(v___x_4035_, 1);
                    v_isSharedCheck_4049_ = (!crate::leanh::lean_is_exclusive(v___x_4035_)) as u8;
                    if v_isSharedCheck_4049_ == 0 {
                        v___x_4039_ = v___x_4035_;
                        v_isShared_4040_ = v_isSharedCheck_4049_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_changesAfter_4037_);
                        crate::leanh::lean_inc(v_changesBefore_4036_);
                        crate::leanh::lean_dec(v___x_4035_);
                        v___x_4039_ = crate::leanh::lean_box(0);
                        v_isShared_4040_ = v_isSharedCheck_4049_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4027_);
                    crate::leanh::lean_dec(v_a_4025_);
                    crate::leanh::lean_dec(v_pos_3979_);
                    crate::leanh::lean_dec(v_pos_3937_);
                    v___x_4050_ = 0;
                    v___x_4051_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_3974_, v_binderInfo_3977_, v_binderType_3975_, v___f_4009_, v___x_4050_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
                    return v___x_4051_;
                }
            }
            20 => {
                v___x_4041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_4030_, v_changesBefore_4036_);
                v___x_4042_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_4031_, v_changesAfter_4037_);
                if v_isShared_4040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4039_, 1, v___x_4042_);
                    crate::leanh::lean_ctor_set(v___x_4039_, 0, v___x_4041_);
                    v___x_4044_ = v___x_4039_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4042_);
                    v___x_4044_ = v_reuseFailAlloc_4048_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4028_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4027_, 0, v___x_4044_);
                    v___x_4046_ = v___x_4027_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4044_);
                    v___x_4046_ = v_reuseFailAlloc_4047_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
    mut v_before_4065_: *mut crate::leanh::LeanObject,
    mut v_after_4066_: *mut crate::leanh::LeanObject,
    mut v_a_4067_: *mut crate::leanh::LeanObject,
    mut v_a_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
    mut v_a_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_u2081_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v_expr_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut v_unused_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u8 = 0;
    let mut v_args_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: usize = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: usize = 0;
    let mut v___x_4157_: usize = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut v_a_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4170_: u8 = 0;
    let mut v_expr_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4177_: u8 = 0;
    let mut v_binderName_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4181_: u8 = 0;
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: u8 = 0;
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4201_: u8 = 0;
    let mut v_changesBefore_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_unused_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: u8 = 0;
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_unused_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v_unused_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_4088_ = crate::leanh::lean_ctor_get(v_before_4065_, 0);
                v_pos_4089_ = crate::leanh::lean_ctor_get(v_before_4065_, 1);
                v_expr_4090_ = crate::leanh::lean_ctor_get(v_after_4066_, 0);
                v_pos_4091_ = crate::leanh::lean_ctor_get(v_after_4066_, 1);
                v___x_4100_ = lean_expr_eqv(v_expr_4088_, v_expr_4090_);
                if v___x_4100_ == 0 {
                    match crate::leanh::lean_obj_tag(v_expr_4088_) {
                        10 => {
                            crate::leanh::lean_inc_ref(v_expr_4088_);
                            crate::leanh::lean_inc(v_pos_4089_);
                            v_isSharedCheck_4109_ =
                                (!crate::leanh::lean_is_exclusive(v_before_4065_)) as u8;
                            if v_isSharedCheck_4109_ == 0 {
                                v_unused_4110_ = crate::leanh::lean_ctor_get(v_before_4065_, 1);
                                crate::leanh::lean_dec(v_unused_4110_);
                                v_unused_4111_ = crate::leanh::lean_ctor_get(v_before_4065_, 0);
                                crate::leanh::lean_dec(v_unused_4111_);
                                v___x_4102_ = v_before_4065_;
                                v_isShared_4103_ = v_isSharedCheck_4109_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_before_4065_);
                                v___x_4102_ = crate::leanh::lean_box(0);
                                v_isShared_4103_ = v_isSharedCheck_4109_;
                                state = 6;
                                continue;
                            }
                        }
                        5 => match crate::leanh::lean_obj_tag(v_expr_4090_) {
                            10 => {
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                crate::leanh::lean_inc(v_pos_4091_);
                                crate::leanh::lean_dec_ref(v_after_4066_);
                                v_expr_4112_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4112_);
                                crate::leanh::lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4112_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            5 => {
                                v_dummy_4113_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
                                v_nargs_4114_ = l_Lean_Expr_getAppNumArgs(v_expr_4090_);
                                crate::leanh::lean_inc(v_nargs_4114_);
                                v___x_4115_ = lean_mk_array(v_nargs_4114_, v_dummy_4113_);
                                v___x_4116_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_4117_ = lean_nat_sub(v_nargs_4114_, v___x_4116_);
                                crate::leanh::lean_dec(v_nargs_4114_);
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                v___x_4118_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_4090_, v___x_4115_, v___x_4117_);
                                v_fst_4119_ = crate::leanh::lean_ctor_get(v___x_4118_, 0);
                                crate::leanh::lean_inc(v_fst_4119_);
                                v_snd_4120_ = crate::leanh::lean_ctor_get(v___x_4118_, 1);
                                crate::leanh::lean_inc(v_snd_4120_);
                                crate::leanh::lean_dec_ref(v___x_4118_);
                                v_nargs_4121_ = l_Lean_Expr_getAppNumArgs(v_expr_4088_);
                                crate::leanh::lean_inc(v_nargs_4121_);
                                v___x_4122_ = lean_mk_array(v_nargs_4121_, v_dummy_4113_);
                                v___x_4123_ = lean_nat_sub(v_nargs_4121_, v___x_4116_);
                                crate::leanh::lean_dec(v_nargs_4121_);
                                crate::leanh::lean_inc_ref(v_expr_4088_);
                                v___x_4124_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_4088_, v___x_4122_, v___x_4123_);
                                v_fst_4125_ = crate::leanh::lean_ctor_get(v___x_4124_, 0);
                                crate::leanh::lean_inc(v_fst_4125_);
                                v_snd_4126_ = crate::leanh::lean_ctor_get(v___x_4124_, 1);
                                crate::leanh::lean_inc(v_snd_4126_);
                                crate::leanh::lean_dec_ref(v___x_4124_);
                                v___x_4127_ = lean_expr_eqv(v_fst_4119_, v_fst_4125_);
                                crate::leanh::lean_dec(v_fst_4125_);
                                crate::leanh::lean_dec(v_fst_4119_);
                                if v___x_4127_ == 0 {
                                    crate::leanh::lean_dec(v_snd_4126_);
                                    crate::leanh::lean_dec(v_snd_4120_);
                                    state = 3;
                                    continue;
                                } else {
                                    if v___x_4100_ == 0 {
                                        v___x_4128_ = lean_array_get_size(v_snd_4120_);
                                        v___x_4129_ = lean_array_get_size(v_snd_4126_);
                                        v___x_4130_ = lean_nat_dec_eq(v___x_4128_, v___x_4129_);
                                        if v___x_4130_ == 0 {
                                            crate::leanh::lean_dec(v_snd_4126_);
                                            crate::leanh::lean_dec(v_snd_4120_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v_args_4131_ =
                                                l_Array_zip___redArg(v_snd_4120_, v_snd_4126_);
                                            crate::leanh::lean_dec(v_snd_4126_);
                                            v___x_4132_ = lean_array_get_size(v_args_4131_);
                                            v___x_4133_ = crate::leanh::lean_unsigned_to_nat(0);
                                            v___x_4134_ =
                                                lean_mk_empty_array_with_capacity(v___x_4132_);
                                            v___x_4135_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4120_, v_before_4065_, v_after_4066_, v_args_4131_, v___x_4132_, v___x_4133_, v___x_4134_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                            crate::leanh::lean_dec_ref(v_args_4131_);
                                            crate::leanh::lean_dec_ref(v_after_4066_);
                                            crate::leanh::lean_dec_ref(v_before_4065_);
                                            crate::leanh::lean_dec(v_snd_4120_);
                                            if crate::leanh::lean_obj_tag(v___x_4135_) == 0 {
                                                v_a_4136_ =
                                                    crate::leanh::lean_ctor_get(v___x_4135_, 0);
                                                v_isSharedCheck_4162_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4135_))
                                                        as u8;
                                                if v_isSharedCheck_4162_ == 0 {
                                                    v___x_4138_ = v___x_4135_;
                                                    v_isShared_4139_ = v_isSharedCheck_4162_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4136_);
                                                    crate::leanh::lean_dec(v___x_4135_);
                                                    v___x_4138_ = crate::leanh::lean_box(0);
                                                    v_isShared_4139_ = v_isSharedCheck_4162_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4163_ =
                                                    crate::leanh::lean_ctor_get(v___x_4135_, 0);
                                                v_isSharedCheck_4170_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4135_))
                                                        as u8;
                                                if v_isSharedCheck_4170_ == 0 {
                                                    v___x_4165_ = v___x_4135_;
                                                    v_isShared_4166_ = v_isSharedCheck_4170_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4163_);
                                                    crate::leanh::lean_dec(v___x_4135_);
                                                    v___x_4165_ = crate::leanh::lean_box(0);
                                                    v_isShared_4166_ = v_isSharedCheck_4170_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_snd_4126_);
                                        crate::leanh::lean_dec(v_snd_4120_);
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                state = 4;
                                continue;
                            }
                        },
                        7 => {
                            if crate::leanh::lean_obj_tag(v_expr_4090_) == 10 {
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                crate::leanh::lean_inc(v_pos_4091_);
                                crate::leanh::lean_dec_ref(v_after_4066_);
                                v_expr_4171_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4171_);
                                crate::leanh::lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4171_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4172_ =
                                    l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(
                                        v_before_4065_,
                                        v_after_4066_,
                                        v_a_4067_,
                                        v_a_4068_,
                                        v_a_4069_,
                                        v_a_4070_,
                                    );
                                return v___x_4172_;
                            }
                        }
                        6 => match crate::leanh::lean_obj_tag(v_expr_4090_) {
                            10 => {
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                crate::leanh::lean_inc(v_pos_4091_);
                                crate::leanh::lean_dec_ref(v_after_4066_);
                                v_expr_4173_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4173_);
                                crate::leanh::lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4173_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            6 => {
                                v_binderName_4174_ = crate::leanh::lean_ctor_get(v_expr_4088_, 0);
                                v_binderType_4175_ = crate::leanh::lean_ctor_get(v_expr_4088_, 1);
                                v_body_4176_ = crate::leanh::lean_ctor_get(v_expr_4088_, 2);
                                v_binderInfo_4177_ = crate::leanh::lean_ctor_get_uint8(
                                    v_expr_4088_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                v_binderName_4178_ = crate::leanh::lean_ctor_get(v_expr_4090_, 0);
                                v_binderType_4179_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                v_body_4180_ = crate::leanh::lean_ctor_get(v_expr_4090_, 2);
                                v_binderInfo_4181_ = crate::leanh::lean_ctor_get_uint8(
                                    v_expr_4090_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                v___x_4182_ = lean_name_eq(v_binderName_4174_, v_binderName_4178_);
                                if v___x_4182_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    if v___x_4100_ == 0 {
                                        v___x_4183_ = l_Lean_instBEqBinderInfo_beq(
                                            v_binderInfo_4177_,
                                            v_binderInfo_4181_,
                                        );
                                        if v___x_4183_ == 0 {
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_body_4180_);
                                            crate::leanh::lean_inc_ref(v_binderType_4179_);
                                            crate::leanh::lean_inc_ref(v_body_4176_);
                                            crate::leanh::lean_inc_ref(v_binderType_4175_);
                                            crate::leanh::lean_inc(v_pos_4091_);
                                            crate::leanh::lean_inc(v_pos_4089_);
                                            v_isSharedCheck_4233_ =
                                                (!crate::leanh::lean_is_exclusive(v_before_4065_))
                                                    as u8;
                                            if v_isSharedCheck_4233_ == 0 {
                                                v_unused_4234_ =
                                                    crate::leanh::lean_ctor_get(v_before_4065_, 1);
                                                crate::leanh::lean_dec(v_unused_4234_);
                                                v_unused_4235_ =
                                                    crate::leanh::lean_ctor_get(v_before_4065_, 0);
                                                crate::leanh::lean_dec(v_unused_4235_);
                                                v___x_4185_ = v_before_4065_;
                                                v_isShared_4186_ = v_isSharedCheck_4233_;
                                                state = 15;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_before_4065_);
                                                v___x_4185_ = crate::leanh::lean_box(0);
                                                v_isShared_4186_ = v_isSharedCheck_4233_;
                                                state = 15;
                                                continue;
                                            }
                                        }
                                    } else {
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                state = 4;
                                continue;
                            }
                        },
                        11 => match crate::leanh::lean_obj_tag(v_expr_4090_) {
                            10 => {
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                crate::leanh::lean_inc(v_pos_4091_);
                                crate::leanh::lean_dec_ref(v_after_4066_);
                                v_expr_4236_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4236_);
                                crate::leanh::lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4236_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            11 => {
                                v_typeName_4237_ = crate::leanh::lean_ctor_get(v_expr_4088_, 0);
                                v_idx_4238_ = crate::leanh::lean_ctor_get(v_expr_4088_, 1);
                                v_struct_4239_ = crate::leanh::lean_ctor_get(v_expr_4088_, 2);
                                v_typeName_4240_ = crate::leanh::lean_ctor_get(v_expr_4090_, 0);
                                v_idx_4241_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                v_struct_4242_ = crate::leanh::lean_ctor_get(v_expr_4090_, 2);
                                v___x_4243_ = lean_name_eq(v_typeName_4237_, v_typeName_4240_);
                                if v___x_4243_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    if v___x_4100_ == 0 {
                                        v___x_4244_ = lean_nat_dec_eq(v_idx_4238_, v_idx_4241_);
                                        if v___x_4244_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_struct_4242_);
                                            crate::leanh::lean_inc_ref(v_struct_4239_);
                                            crate::leanh::lean_inc(v_pos_4091_);
                                            crate::leanh::lean_inc(v_pos_4089_);
                                            v_isSharedCheck_4263_ =
                                                (!crate::leanh::lean_is_exclusive(v_before_4065_))
                                                    as u8;
                                            if v_isSharedCheck_4263_ == 0 {
                                                v_unused_4264_ =
                                                    crate::leanh::lean_ctor_get(v_before_4065_, 1);
                                                crate::leanh::lean_dec(v_unused_4264_);
                                                v_unused_4265_ =
                                                    crate::leanh::lean_ctor_get(v_before_4065_, 0);
                                                crate::leanh::lean_dec(v_unused_4265_);
                                                v___x_4246_ = v_before_4065_;
                                                v_isShared_4247_ = v_isSharedCheck_4263_;
                                                state = 23;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_before_4065_);
                                                v___x_4246_ = crate::leanh::lean_box(0);
                                                v_isShared_4247_ = v_isSharedCheck_4263_;
                                                state = 23;
                                                continue;
                                            }
                                        }
                                    } else {
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                state = 4;
                                continue;
                            }
                        },
                        _ => {
                            if crate::leanh::lean_obj_tag(v_expr_4090_) == 10 {
                                crate::leanh::lean_inc_ref(v_expr_4090_);
                                crate::leanh::lean_inc(v_pos_4091_);
                                crate::leanh::lean_dec_ref(v_after_4066_);
                                v_expr_4266_ = crate::leanh::lean_ctor_get(v_expr_4090_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4266_);
                                crate::leanh::lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4266_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            } else {
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_after_4066_);
                    crate::leanh::lean_dec_ref(v_before_4065_);
                    v___x_4267_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                    v___x_4268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4267_);
                    return v___x_4268_;
                }
            }
            1 => {
                v___x_4073_ = 0;
                v___x_4074_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4073_,
                );
                v___x_4075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4074_);
                return v___x_4075_;
            }
            2 => {
                v___x_4077_ = 0;
                v___x_4078_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4077_,
                );
                v___x_4079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4078_);
                return v___x_4079_;
            }
            3 => {
                v___x_4081_ = 0;
                v___x_4082_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4081_,
                );
                v___x_4083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4083_, 0, v___x_4082_);
                return v___x_4083_;
            }
            4 => {
                v___x_4085_ = 0;
                v___x_4086_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4085_,
                );
                v___x_4087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                return v___x_4087_;
            }
            5 => {
                v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4098_, 0, v_e_u2081_4093_);
                crate::leanh::lean_ctor_set(v___x_4098_, 1, v_pos_4091_);
                v_after_4066_ = v___x_4098_;
                v_a_4067_ = v___y_4094_;
                v_a_4068_ = v___y_4095_;
                v_a_4069_ = v___y_4096_;
                v_a_4070_ = v___y_4097_;
                state = 0;
                continue;
            }
            6 => {
                v_expr_4104_ = crate::leanh::lean_ctor_get(v_expr_4088_, 1);
                crate::leanh::lean_inc_ref(v_expr_4104_);
                crate::leanh::lean_dec_ref_known(v_expr_4088_, 2);
                if v_isShared_4103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4102_, 0, v_expr_4104_);
                    v___x_4106_ = v___x_4102_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_expr_4104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_pos_4089_);
                    v___x_4106_ = v_reuseFailAlloc_4108_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_before_4065_ = v___x_4106_;
                state = 0;
                continue;
            }
            8 => {
                v___x_4140_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                v___x_4141_ = lean_array_get_size(v_a_4136_);
                v___x_4142_ = lean_nat_dec_lt(v___x_4133_, v___x_4141_);
                if v___x_4142_ == 0 {
                    crate::leanh::lean_dec(v_a_4136_);
                    if v_isShared_4139_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4140_);
                        v___x_4144_ = v___x_4138_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4140_);
                        v___x_4144_ = v_reuseFailAlloc_4145_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_4146_ = lean_nat_dec_le(v___x_4141_, v___x_4141_);
                    if v___x_4146_ == 0 {
                        if v___x_4142_ == 0 {
                            crate::leanh::lean_dec(v_a_4136_);
                            if v_isShared_4139_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4140_);
                                v___x_4148_ = v___x_4138_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4149_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4140_);
                                v___x_4148_ = v_reuseFailAlloc_4149_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___x_4150_ = 0usize;
                            v___x_4151_ = lean_usize_of_nat(v___x_4141_);
                            v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_4136_, v___x_4150_, v___x_4151_, v___x_4140_);
                            crate::leanh::lean_dec(v_a_4136_);
                            if v_isShared_4139_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4152_);
                                v___x_4154_ = v___x_4138_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_4155_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                                v___x_4154_ = v_reuseFailAlloc_4155_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_4156_ = 0usize;
                        v___x_4157_ = lean_usize_of_nat(v___x_4141_);
                        v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_4136_, v___x_4156_, v___x_4157_, v___x_4140_);
                        crate::leanh::lean_dec(v_a_4136_);
                        if v_isShared_4139_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4158_);
                            v___x_4160_ = v___x_4138_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4161_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
                            v___x_4160_ = v_reuseFailAlloc_4161_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            9 => {
                return v___x_4144_;
            }
            10 => {
                return v___x_4148_;
            }
            11 => {
                return v___x_4154_;
            }
            12 => {
                return v___x_4160_;
            }
            13 => {
                if v_isShared_4166_ == 0 {
                    v___x_4168_ = v___x_4165_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4169_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
                    v___x_4168_ = v_reuseFailAlloc_4169_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4168_;
            }
            15 => {
                v_isSharedCheck_4230_ = (!crate::leanh::lean_is_exclusive(v_after_4066_)) as u8;
                if v_isSharedCheck_4230_ == 0 {
                    v_unused_4231_ = crate::leanh::lean_ctor_get(v_after_4066_, 1);
                    crate::leanh::lean_dec(v_unused_4231_);
                    v_unused_4232_ = crate::leanh::lean_ctor_get(v_after_4066_, 0);
                    crate::leanh::lean_dec(v_unused_4232_);
                    v___x_4188_ = v_after_4066_;
                    v_isShared_4189_ = v_isSharedCheck_4230_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_after_4066_);
                    v___x_4188_ = crate::leanh::lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4230_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4190_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_4089_);
                if v_isShared_4189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4188_, 1, v___x_4190_);
                    crate::leanh::lean_ctor_set(v___x_4188_, 0, v_binderType_4175_);
                    v___x_4192_ = v___x_4188_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_binderType_4175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4190_);
                    v___x_4192_ = v_reuseFailAlloc_4229_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4193_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_4091_);
                if v_isShared_4186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4185_, 1, v___x_4193_);
                    crate::leanh::lean_ctor_set(v___x_4185_, 0, v_binderType_4179_);
                    v___x_4195_ = v___x_4185_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_binderType_4179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4193_);
                    v___x_4195_ = v_reuseFailAlloc_4228_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4196_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                    v___x_4192_,
                    v___x_4195_,
                    v_a_4067_,
                    v_a_4068_,
                    v_a_4069_,
                    v_a_4070_,
                );
                if crate::leanh::lean_obj_tag(v___x_4196_) == 0 {
                    v_a_4197_ = crate::leanh::lean_ctor_get(v___x_4196_, 0);
                    v_isSharedCheck_4227_ = (!crate::leanh::lean_is_exclusive(v___x_4196_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4199_ = v___x_4196_;
                        v_isShared_4200_ = v_isSharedCheck_4227_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4197_);
                        crate::leanh::lean_dec(v___x_4196_);
                        v___x_4199_ = crate::leanh::lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4227_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_4180_);
                    crate::leanh::lean_dec_ref(v_body_4176_);
                    crate::leanh::lean_dec(v_pos_4091_);
                    crate::leanh::lean_dec(v_pos_4089_);
                    return v___x_4196_;
                }
            }
            19 => {
                v___x_4201_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_4197_);
                if v___x_4201_ == 0 {
                    crate::leanh::lean_dec_ref(v_body_4180_);
                    crate::leanh::lean_dec_ref(v_body_4176_);
                    v_changesBefore_4202_ = crate::leanh::lean_ctor_get(v_a_4197_, 0);
                    crate::leanh::lean_inc(v_changesBefore_4202_);
                    v_changesAfter_4203_ = crate::leanh::lean_ctor_get(v_a_4197_, 1);
                    crate::leanh::lean_inc(v_changesAfter_4203_);
                    crate::leanh::lean_dec(v_a_4197_);
                    v___x_4204_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4089_);
                    crate::leanh::lean_dec(v_pos_4089_);
                    v___x_4205_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4091_);
                    crate::leanh::lean_dec(v_pos_4091_);
                    v___x_4206_ = 0;
                    v___x_4207_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
                            v___x_4204_,
                            v___x_4205_,
                            v___x_4206_,
                        );
                    v_changesBefore_4208_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                    v_changesAfter_4209_ = crate::leanh::lean_ctor_get(v___x_4207_, 1);
                    v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4211_ = v___x_4207_;
                        v_isShared_4212_ = v_isSharedCheck_4221_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_changesAfter_4209_);
                        crate::leanh::lean_inc(v_changesBefore_4208_);
                        crate::leanh::lean_dec(v___x_4207_);
                        v___x_4211_ = crate::leanh::lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4221_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4199_);
                    crate::leanh::lean_dec(v_a_4197_);
                    v___x_4222_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4089_);
                    crate::leanh::lean_dec(v_pos_4089_);
                    v___x_4223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4223_, 0, v_body_4176_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                    v___x_4224_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4091_);
                    crate::leanh::lean_dec(v_pos_4091_);
                    v___x_4225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4225_, 0, v_body_4180_);
                    crate::leanh::lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                    v_before_4065_ = v___x_4223_;
                    v_after_4066_ = v___x_4225_;
                    state = 0;
                    continue;
                }
            }
            20 => {
                v___x_4213_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_4202_, v_changesBefore_4208_);
                v___x_4214_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_4203_, v_changesAfter_4209_);
                if v_isShared_4212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4211_, 1, v___x_4214_);
                    crate::leanh::lean_ctor_set(v___x_4211_, 0, v___x_4213_);
                    v___x_4216_ = v___x_4211_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4214_);
                    v___x_4216_ = v_reuseFailAlloc_4220_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4216_);
                    v___x_4218_ = v___x_4199_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4218_;
            }
            23 => {
                v_isSharedCheck_4260_ = (!crate::leanh::lean_is_exclusive(v_after_4066_)) as u8;
                if v_isSharedCheck_4260_ == 0 {
                    v_unused_4261_ = crate::leanh::lean_ctor_get(v_after_4066_, 1);
                    crate::leanh::lean_dec(v_unused_4261_);
                    v_unused_4262_ = crate::leanh::lean_ctor_get(v_after_4066_, 0);
                    crate::leanh::lean_dec(v_unused_4262_);
                    v___x_4249_ = v_after_4066_;
                    v_isShared_4250_ = v_isSharedCheck_4260_;
                    state = 24;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_after_4066_);
                    v___x_4249_ = crate::leanh::lean_box(0);
                    v_isShared_4250_ = v_isSharedCheck_4260_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4251_ = l_Lean_SubExpr_Pos_pushProj(v_pos_4089_);
                crate::leanh::lean_dec(v_pos_4089_);
                if v_isShared_4250_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4249_, 1, v___x_4251_);
                    crate::leanh::lean_ctor_set(v___x_4249_, 0, v_struct_4239_);
                    v___x_4253_ = v___x_4249_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_struct_4239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 1, v___x_4251_);
                    v___x_4253_ = v_reuseFailAlloc_4259_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4254_ = l_Lean_SubExpr_Pos_pushProj(v_pos_4091_);
                crate::leanh::lean_dec(v_pos_4091_);
                if v_isShared_4247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4254_);
                    crate::leanh::lean_ctor_set(v___x_4246_, 0, v_struct_4242_);
                    v___x_4256_ = v___x_4246_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_struct_4242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 1, v___x_4254_);
                    v___x_4256_ = v_reuseFailAlloc_4258_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v_before_4065_ = v___x_4253_;
                v_after_4066_ = v___x_4256_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0(
    mut v_body_4269_: *mut crate::leanh::LeanObject,
    mut v_pos_4270_: *mut crate::leanh::LeanObject,
    mut v_body_4271_: *mut crate::leanh::LeanObject,
    mut v_pos_4272_: *mut crate::leanh::LeanObject,
    mut v_x_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4279_ = lean_expr_instantiate1(v_body_4269_, v_x_4273_);
    v___x_4280_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4270_);
    v___x_4281_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4281_, 0, v___x_4279_);
    crate::leanh::lean_ctor_set(v___x_4281_, 1, v___x_4280_);
    v___x_4282_ = lean_expr_instantiate1(v_body_4271_, v_x_4273_);
    v___x_4283_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4272_);
    v___x_4284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4284_, 0, v___x_4282_);
    crate::leanh::lean_ctor_set(v___x_4284_, 1, v___x_4283_);
    v___x_4285_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
        v___x_4281_,
        v___x_4284_,
        v___y_4274_,
        v___y_4275_,
        v___y_4276_,
        v___y_4277_,
    );
    return v___x_4285_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg___boxed(
    mut v_snd_4286_: *mut crate::leanh::LeanObject,
    mut v_before_4287_: *mut crate::leanh::LeanObject,
    mut v_after_4288_: *mut crate::leanh::LeanObject,
    mut v_as_4289_: *mut crate::leanh::LeanObject,
    mut v_i_4290_: *mut crate::leanh::LeanObject,
    mut v_j_4291_: *mut crate::leanh::LeanObject,
    mut v_bs_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4298_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4286_, v_before_4287_, v_after_4288_, v_as_4289_, v_i_4290_, v_j_4291_, v_bs_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
    crate::leanh::lean_dec(v___y_4296_);
    crate::leanh::lean_dec_ref(v___y_4295_);
    crate::leanh::lean_dec(v___y_4294_);
    crate::leanh::lean_dec_ref(v___y_4293_);
    crate::leanh::lean_dec_ref(v_as_4289_);
    crate::leanh::lean_dec_ref(v_after_4288_);
    crate::leanh::lean_dec_ref(v_before_4287_);
    crate::leanh::lean_dec_ref(v_snd_4286_);
    return v_res_4298_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(
    mut v_before_4299_: *mut crate::leanh::LeanObject,
    mut v_after_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
    mut v_a_4303_: *mut crate::leanh::LeanObject,
    mut v_a_4304_: *mut crate::leanh::LeanObject,
    mut v_a_4305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4306_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(
        v_before_4299_,
        v_after_4300_,
        v_a_4301_,
        v_a_4302_,
        v_a_4303_,
        v_a_4304_,
    );
    crate::leanh::lean_dec(v_a_4304_);
    crate::leanh::lean_dec_ref(v_a_4303_);
    crate::leanh::lean_dec(v_a_4302_);
    crate::leanh::lean_dec_ref(v_a_4301_);
    return v_res_4306_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(
    mut v_before_4307_: *mut crate::leanh::LeanObject,
    mut v_after_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
        v_before_4307_,
        v_after_4308_,
        v_a_4309_,
        v_a_4310_,
        v_a_4311_,
        v_a_4312_,
    );
    crate::leanh::lean_dec(v_a_4312_);
    crate::leanh::lean_dec_ref(v_a_4311_);
    crate::leanh::lean_dec(v_a_4310_);
    crate::leanh::lean_dec_ref(v_a_4309_);
    return v_res_4314_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(
    mut v_upperBound_4315_: *mut crate::leanh::LeanObject,
    mut v_before_4316_: *mut crate::leanh::LeanObject,
    mut v_inst_4317_: *mut crate::leanh::LeanObject,
    mut v_R_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_b_4320_: *mut crate::leanh::LeanObject,
    mut v_c_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_4315_, v_before_4316_, v_a_4319_, v_b_4320_);
    return v___x_4327_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(
    mut v_upperBound_4328_: *mut crate::leanh::LeanObject,
    mut v_before_4329_: *mut crate::leanh::LeanObject,
    mut v_inst_4330_: *mut crate::leanh::LeanObject,
    mut v_R_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
    mut v_b_4333_: *mut crate::leanh::LeanObject,
    mut v_c_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_4328_, v_before_4329_, v_inst_4330_, v_R_4331_, v_a_4332_, v_b_4333_, v_c_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
    crate::leanh::lean_dec(v___y_4338_);
    crate::leanh::lean_dec_ref(v___y_4337_);
    crate::leanh::lean_dec(v___y_4336_);
    crate::leanh::lean_dec_ref(v___y_4335_);
    crate::leanh::lean_dec(v_upperBound_4328_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(
    mut v_00_u03b1_4341_: *mut crate::leanh::LeanObject,
    mut v_msg_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4348_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
    return v___x_4348_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(
    mut v_00_u03b1_4349_: *mut crate::leanh::LeanObject,
    mut v_msg_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4356_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_4349_, v_msg_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
    crate::leanh::lean_dec(v___y_4354_);
    crate::leanh::lean_dec_ref(v___y_4353_);
    crate::leanh::lean_dec(v___y_4352_);
    crate::leanh::lean_dec_ref(v___y_4351_);
    return v_res_4356_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(
    mut v_b_u2082_4357_: u8,
    mut v_k_4358_: *mut crate::leanh::LeanObject,
    mut v_t_4359_: *mut crate::leanh::LeanObject,
    mut v_hl_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4361_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_4357_, v_k_4358_, v_t_4359_);
    return v___x_4361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(
    mut v_b_u2082_4362_: *mut crate::leanh::LeanObject,
    mut v_k_4363_: *mut crate::leanh::LeanObject,
    mut v_t_4364_: *mut crate::leanh::LeanObject,
    mut v_hl_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_u2082_boxed_4366_: u8 = 0;
    let mut v_res_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_4366_ = (crate::leanh::lean_unbox(v_b_u2082_4362_) as u8);
    v_res_4367_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_4366_, v_k_4363_, v_t_4364_, v_hl_4365_);
    return v_res_4367_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(
    mut v_init_4368_: *mut crate::leanh::LeanObject,
    mut v_t_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4370_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_4368_, v_t_4369_);
    return v___x_4370_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(
    mut v_snd_4371_: *mut crate::leanh::LeanObject,
    mut v_before_4372_: *mut crate::leanh::LeanObject,
    mut v_after_4373_: *mut crate::leanh::LeanObject,
    mut v_as_4374_: *mut crate::leanh::LeanObject,
    mut v_i_4375_: *mut crate::leanh::LeanObject,
    mut v_j_4376_: *mut crate::leanh::LeanObject,
    mut v_inv_4377_: *mut crate::leanh::LeanObject,
    mut v_bs_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
    mut v___y_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4371_, v_before_4372_, v_after_4373_, v_as_4374_, v_i_4375_, v_j_4376_, v_bs_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
    return v___x_4384_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(
    mut v_snd_4385_: *mut crate::leanh::LeanObject,
    mut v_before_4386_: *mut crate::leanh::LeanObject,
    mut v_after_4387_: *mut crate::leanh::LeanObject,
    mut v_as_4388_: *mut crate::leanh::LeanObject,
    mut v_i_4389_: *mut crate::leanh::LeanObject,
    mut v_j_4390_: *mut crate::leanh::LeanObject,
    mut v_inv_4391_: *mut crate::leanh::LeanObject,
    mut v_bs_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_4385_, v_before_4386_, v_after_4387_, v_as_4388_, v_i_4389_, v_j_4390_, v_inv_4391_, v_bs_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
    crate::leanh::lean_dec(v___y_4396_);
    crate::leanh::lean_dec_ref(v___y_4395_);
    crate::leanh::lean_dec(v___y_4394_);
    crate::leanh::lean_dec_ref(v___y_4393_);
    crate::leanh::lean_dec_ref(v_as_4388_);
    crate::leanh::lean_dec_ref(v_after_4387_);
    crate::leanh::lean_dec_ref(v_before_4386_);
    crate::leanh::lean_dec_ref(v_snd_4385_);
    return v_res_4398_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
    mut v_e_u2080_4399_: *mut crate::leanh::LeanObject,
    mut v_e_u2081_4400_: *mut crate::leanh::LeanObject,
    mut v_useAfter_4401_: u8,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_u2080_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = l_Lean_SubExpr_Pos_root;
    v_s_u2080_4408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_s_u2080_4408_, 0, v_e_u2080_4399_);
    crate::leanh::lean_ctor_set(v_s_u2080_4408_, 1, v___x_4407_);
    v_s_u2081_4409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_s_u2081_4409_, 0, v_e_u2081_4400_);
    crate::leanh::lean_ctor_set(v_s_u2081_4409_, 1, v___x_4407_);
    if v_useAfter_4401_ == 0 {
        let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4410_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
            v_s_u2081_4409_,
            v_s_u2080_4408_,
            v_a_4402_,
            v_a_4403_,
            v_a_4404_,
            v_a_4405_,
        );
        return v___x_4410_;
    } else {
        let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4411_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
            v_s_u2080_4408_,
            v_s_u2081_4409_,
            v_a_4402_,
            v_a_4403_,
            v_a_4404_,
            v_a_4405_,
        );
        return v___x_4411_;
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff___boxed(
    mut v_e_u2080_4412_: *mut crate::leanh::LeanObject,
    mut v_e_u2081_4413_: *mut crate::leanh::LeanObject,
    mut v_useAfter_4414_: *mut crate::leanh::LeanObject,
    mut v_a_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_4420_: u8 = 0;
    let mut v_res_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4420_ = (crate::leanh::lean_unbox(v_useAfter_4414_) as u8);
    v_res_4421_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
        v_e_u2080_4412_,
        v_e_u2081_4413_,
        v_useAfter_boxed_4420_,
        v_a_4415_,
        v_a_4416_,
        v_a_4417_,
        v_a_4418_,
    );
    crate::leanh::lean_dec(v_a_4418_);
    crate::leanh::lean_dec_ref(v_a_4417_);
    crate::leanh::lean_dec(v_a_4416_);
    crate::leanh::lean_dec_ref(v_a_4415_);
    return v_res_4421_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(
    mut v_useAfter_4422_: u8,
    mut v_info_4423_: *mut crate::leanh::LeanObject,
    mut v_d_4424_: u8,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(
        v_useAfter_4422_,
        v_d_4424_,
    );
    v___x_4431_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_4430_, v_info_4423_);
    v___x_4432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4432_, 0, v___x_4431_);
    return v___x_4432_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(
    mut v_useAfter_4433_: *mut crate::leanh::LeanObject,
    mut v_info_4434_: *mut crate::leanh::LeanObject,
    mut v_d_4435_: *mut crate::leanh::LeanObject,
    mut v___y_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_4441_: u8 = 0;
    let mut v_d_boxed_4442_: u8 = 0;
    let mut v_res_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4441_ = (crate::leanh::lean_unbox(v_useAfter_4433_) as u8);
    v_d_boxed_4442_ = (crate::leanh::lean_unbox(v_d_4435_) as u8);
    v_res_4443_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(
        v_useAfter_boxed_4441_,
        v_info_4434_,
        v_d_boxed_4442_,
        v___y_4436_,
        v___y_4437_,
        v___y_4438_,
        v___y_4439_,
    );
    crate::leanh::lean_dec(v___y_4439_);
    crate::leanh::lean_dec_ref(v___y_4438_);
    crate::leanh::lean_dec(v___y_4437_);
    crate::leanh::lean_dec_ref(v___y_4436_);
    return v_res_4443_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(
    mut v_f_4444_: *mut crate::leanh::LeanObject,
    mut v_x_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4459_: u8 = 0;
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v_sz_4464_: usize = 0;
    let mut v___x_4465_: usize = 0;
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_a_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v_a_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_a_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4445_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_f_4444_);
                    v_a_4451_ = crate::leanh::lean_ctor_get(v_x_4445_, 0);
                    v_isSharedCheck_4459_ = (!crate::leanh::lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4459_ == 0 {
                        v___x_4453_ = v_x_4445_;
                        v_isShared_4454_ = v_isSharedCheck_4459_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4451_);
                        crate::leanh::lean_dec(v_x_4445_);
                        v___x_4453_ = crate::leanh::lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4459_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4460_ = crate::leanh::lean_ctor_get(v_x_4445_, 0);
                    v_isSharedCheck_4486_ = (!crate::leanh::lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4486_ == 0 {
                        v___x_4462_ = v_x_4445_;
                        v_isShared_4463_ = v_isSharedCheck_4486_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4460_);
                        crate::leanh::lean_dec(v_x_4445_);
                        v___x_4462_ = crate::leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4486_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4487_ = crate::leanh::lean_ctor_get(v_x_4445_, 0);
                    v_a_4488_ = crate::leanh::lean_ctor_get(v_x_4445_, 1);
                    v_isSharedCheck_4514_ = (!crate::leanh::lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4490_ = v_x_4445_;
                        v_isShared_4491_ = v_isSharedCheck_4514_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4488_);
                        crate::leanh::lean_inc(v_a_4487_);
                        crate::leanh::lean_dec(v_x_4445_);
                        v___x_4490_ = crate::leanh::lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4514_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_4454_ == 0 {
                    v___x_4456_ = v___x_4453_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4456_);
                return v___x_4457_;
            }
            3 => {
                v_sz_4464_ = lean_array_size(v_a_4460_);
                v___x_4465_ = 0usize;
                v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4444_, v_sz_4464_, v___x_4465_, v_a_4460_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
                if crate::leanh::lean_obj_tag(v___x_4466_) == 0 {
                    v_a_4467_ = crate::leanh::lean_ctor_get(v___x_4466_, 0);
                    v_isSharedCheck_4477_ = (!crate::leanh::lean_is_exclusive(v___x_4466_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4469_ = v___x_4466_;
                        v_isShared_4470_ = v_isSharedCheck_4477_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4467_);
                        crate::leanh::lean_dec(v___x_4466_);
                        v___x_4469_ = crate::leanh::lean_box(0);
                        v_isShared_4470_ = v_isSharedCheck_4477_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4462_);
                    v_a_4478_ = crate::leanh::lean_ctor_get(v___x_4466_, 0);
                    v_isSharedCheck_4485_ = (!crate::leanh::lean_is_exclusive(v___x_4466_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4480_ = v___x_4466_;
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4478_);
                        crate::leanh::lean_dec(v___x_4466_);
                        v___x_4480_ = crate::leanh::lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4462_, 0, v_a_4467_);
                    v___x_4472_ = v___x_4462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4470_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4469_, 0, v___x_4472_);
                    v___x_4474_ = v___x_4469_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4472_);
                    v___x_4474_ = v_reuseFailAlloc_4475_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4474_;
            }
            7 => {
                if v_isShared_4481_ == 0 {
                    v___x_4483_ = v___x_4480_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4483_;
            }
            9 => {
                crate::leanh::lean_inc_ref(v_f_4444_);
                crate::leanh::lean_inc(v___y_4449_);
                crate::leanh::lean_inc_ref(v___y_4448_);
                crate::leanh::lean_inc(v___y_4447_);
                crate::leanh::lean_inc_ref(v___y_4446_);
                v___x_4492_ = crate::leanh::lean_apply_6(
                    v_f_4444_,
                    v_a_4487_,
                    v___y_4446_,
                    v___y_4447_,
                    v___y_4448_,
                    v___y_4449_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4492_) == 0 {
                    v_a_4493_ = crate::leanh::lean_ctor_get(v___x_4492_, 0);
                    crate::leanh::lean_inc(v_a_4493_);
                    crate::leanh::lean_dec_ref_known(v___x_4492_, 1);
                    v___x_4494_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4444_, v_a_4488_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
                    if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
                        v_a_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                        v_isSharedCheck_4505_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
                        if v_isSharedCheck_4505_ == 0 {
                            v___x_4497_ = v___x_4494_;
                            v_isShared_4498_ = v_isSharedCheck_4505_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4495_);
                            crate::leanh::lean_dec(v___x_4494_);
                            v___x_4497_ = crate::leanh::lean_box(0);
                            v_isShared_4498_ = v_isSharedCheck_4505_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4493_);
                        crate::leanh::lean_del_object(v___x_4490_);
                        return v___x_4494_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4490_);
                    crate::leanh::lean_dec_ref(v_a_4488_);
                    crate::leanh::lean_dec_ref(v_f_4444_);
                    v_a_4506_ = crate::leanh::lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4513_ = (!crate::leanh::lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4508_ = v___x_4492_;
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4506_);
                        crate::leanh::lean_dec(v___x_4492_);
                        v___x_4508_ = crate::leanh::lean_box(0);
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4490_, 1, v_a_4495_);
                    crate::leanh::lean_ctor_set(v___x_4490_, 0, v_a_4493_);
                    v___x_4500_ = v___x_4490_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4504_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_a_4495_);
                    v___x_4500_ = v_reuseFailAlloc_4504_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4497_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4502_;
            }
            13 => {
                if v_isShared_4509_ == 0 {
                    v___x_4511_ = v___x_4508_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
                    v___x_4511_ = v_reuseFailAlloc_4512_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(
    mut v_f_4515_: *mut crate::leanh::LeanObject,
    mut v_sz_4516_: usize,
    mut v_i_4517_: usize,
    mut v_bs_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: usize = 0;
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4524_ = lean_usize_dec_lt(v_i_4517_, v_sz_4516_);
                if v___x_4524_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_4515_);
                    v___x_4525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4525_, 0, v_bs_4518_);
                    return v___x_4525_;
                } else {
                    v_v_4526_ = lean_array_uget_borrowed(v_bs_4518_, v_i_4517_);
                    crate::leanh::lean_inc(v_v_4526_);
                    crate::leanh::lean_inc_ref(v_f_4515_);
                    v___x_4527_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4515_, v_v_4526_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
                    if crate::leanh::lean_obj_tag(v___x_4527_) == 0 {
                        v_a_4528_ = crate::leanh::lean_ctor_get(v___x_4527_, 0);
                        crate::leanh::lean_inc(v_a_4528_);
                        crate::leanh::lean_dec_ref_known(v___x_4527_, 1);
                        v___x_4529_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4530_ = lean_array_uset(v_bs_4518_, v_i_4517_, v___x_4529_);
                        v___x_4531_ = 1usize;
                        v___x_4532_ = lean_usize_add(v_i_4517_, v___x_4531_);
                        v___x_4533_ = lean_array_uset(v_bs_x27_4530_, v_i_4517_, v_a_4528_);
                        v_i_4517_ = v___x_4532_;
                        v_bs_4518_ = v___x_4533_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4518_);
                        crate::leanh::lean_dec_ref(v_f_4515_);
                        v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4527_, 0);
                        v_isSharedCheck_4542_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4527_)) as u8;
                        if v_isSharedCheck_4542_ == 0 {
                            v___x_4537_ = v___x_4527_;
                            v_isShared_4538_ = v_isSharedCheck_4542_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4535_);
                            crate::leanh::lean_dec(v___x_4527_);
                            v___x_4537_ = crate::leanh::lean_box(0);
                            v_isShared_4538_ = v_isSharedCheck_4542_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4538_ == 0 {
                    v___x_4540_ = v___x_4537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
                    v___x_4540_ = v_reuseFailAlloc_4541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_f_4543_: *mut crate::leanh::LeanObject,
    mut v_sz_4544_: *mut crate::leanh::LeanObject,
    mut v_i_4545_: *mut crate::leanh::LeanObject,
    mut v_bs_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4552_: usize = 0;
    let mut v_i_boxed_4553_: usize = 0;
    let mut v_res_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4552_ = crate::leanh::lean_unbox_usize(v_sz_4544_);
    crate::leanh::lean_dec(v_sz_4544_);
    v_i_boxed_4553_ = crate::leanh::lean_unbox_usize(v_i_4545_);
    crate::leanh::lean_dec(v_i_4545_);
    v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4543_, v_sz_boxed_4552_, v_i_boxed_4553_, v_bs_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
    crate::leanh::lean_dec(v___y_4550_);
    crate::leanh::lean_dec_ref(v___y_4549_);
    crate::leanh::lean_dec(v___y_4548_);
    crate::leanh::lean_dec_ref(v___y_4547_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(
    mut v_f_4555_: *mut crate::leanh::LeanObject,
    mut v_x_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4562_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4555_, v_x_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
    crate::leanh::lean_dec(v___y_4560_);
    crate::leanh::lean_dec_ref(v___y_4559_);
    crate::leanh::lean_dec(v___y_4558_);
    crate::leanh::lean_dec_ref(v___y_4557_);
    return v_res_4562_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(
    mut v_t_4563_: *mut crate::leanh::LeanObject,
    mut v_k_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4563_) == 0 {
                    v_k_4565_ = crate::leanh::lean_ctor_get(v_t_4563_, 1);
                    v_v_4566_ = crate::leanh::lean_ctor_get(v_t_4563_, 2);
                    v_l_4567_ = crate::leanh::lean_ctor_get(v_t_4563_, 3);
                    v_r_4568_ = crate::leanh::lean_ctor_get(v_t_4563_, 4);
                    v___x_4569_ = lean_nat_dec_lt(v_k_4564_, v_k_4565_);
                    if v___x_4569_ == 0 {
                        v___x_4570_ = lean_nat_dec_eq(v_k_4564_, v_k_4565_);
                        if v___x_4570_ == 0 {
                            v_t_4563_ = v_r_4568_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_4566_);
                            v___x_4572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4572_, 0, v_v_4566_);
                            return v___x_4572_;
                        }
                    } else {
                        v_t_4563_ = v_l_4567_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_4574_ = crate::leanh::lean_box(0);
                    return v___x_4574_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(
    mut v_t_4575_: *mut crate::leanh::LeanObject,
    mut v_k_4576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_4575_, v_k_4576_);
    crate::leanh::lean_dec(v_k_4576_);
    crate::leanh::lean_dec(v_t_4575_);
    return v_res_4577_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(
    mut v_pm_4578_: *mut crate::leanh::LeanObject,
    mut v_merger_4579_: *mut crate::leanh::LeanObject,
    mut v_info_4580_: *mut crate::leanh::LeanObject,
    mut v___y_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subexprPos_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subexprPos_4586_ = crate::leanh::lean_ctor_get(v_info_4580_, 1);
    v___x_4587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_4578_, v_subexprPos_4586_);
    if crate::leanh::lean_obj_tag(v___x_4587_) == 0 {
        let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_merger_4579_);
        v___x_4588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4588_, 0, v_info_4580_);
        return v___x_4588_;
    } else {
        let mut v_val_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4589_ = crate::leanh::lean_ctor_get(v___x_4587_, 0);
        crate::leanh::lean_inc(v_val_4589_);
        crate::leanh::lean_dec_ref_known(v___x_4587_, 1);
        crate::leanh::lean_inc(v___y_4584_);
        crate::leanh::lean_inc_ref(v___y_4583_);
        crate::leanh::lean_inc(v___y_4582_);
        crate::leanh::lean_inc_ref(v___y_4581_);
        v___x_4590_ = crate::leanh::lean_apply_7(
            v_merger_4579_,
            v_info_4580_,
            v_val_4589_,
            v___y_4581_,
            v___y_4582_,
            v___y_4583_,
            v___y_4584_,
            crate::leanh::lean_box(0),
        );
        return v___x_4590_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(
    mut v_pm_4591_: *mut crate::leanh::LeanObject,
    mut v_merger_4592_: *mut crate::leanh::LeanObject,
    mut v_info_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_4591_, v_merger_4592_, v_info_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
    crate::leanh::lean_dec(v___y_4597_);
    crate::leanh::lean_dec_ref(v___y_4596_);
    crate::leanh::lean_dec(v___y_4595_);
    crate::leanh::lean_dec_ref(v___y_4594_);
    crate::leanh::lean_dec(v_pm_4591_);
    return v_res_4599_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(
    mut v_merger_4600_: *mut crate::leanh::LeanObject,
    mut v_pm_4601_: *mut crate::leanh::LeanObject,
    mut v_tt_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_pm_4601_) == 0 {
        let mut v___f_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_4608_ = crate::leanh::lean_alloc_closure(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
        crate::leanh::lean_closure_set(v___f_4608_, 0, v_pm_4601_);
        crate::leanh::lean_closure_set(v___f_4608_, 1, v_merger_4600_);
        v___x_4609_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_4608_, v_tt_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
        return v___x_4609_;
    } else {
        let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_merger_4600_);
        v___x_4610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4610_, 0, v_tt_4602_);
        return v___x_4610_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(
    mut v_merger_4611_: *mut crate::leanh::LeanObject,
    mut v_pm_4612_: *mut crate::leanh::LeanObject,
    mut v_tt_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_4611_, v_pm_4612_, v_tt_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
    crate::leanh::lean_dec(v___y_4617_);
    crate::leanh::lean_dec_ref(v___y_4616_);
    crate::leanh::lean_dec(v___y_4615_);
    crate::leanh::lean_dec_ref(v___y_4614_);
    return v_res_4619_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
    mut v_useAfter_4620_: u8,
    mut v_diff_4621_: *mut crate::leanh::LeanObject,
    mut v_info_u2081_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = crate::leanh::lean_box((v_useAfter_4620_) as usize);
    v___f_4629_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed
            as *mut core::ffi::c_void,
        8,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4629_, 0, v___x_4628_);
    if v_useAfter_4620_ == 0 {
        let mut v_changesBefore_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_changesBefore_4630_ = crate::leanh::lean_ctor_get(v_diff_4621_, 0);
        crate::leanh::lean_inc(v_changesBefore_4630_);
        crate::leanh::lean_dec_ref(v_diff_4621_);
        v___x_4631_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_4629_, v_changesBefore_4630_, v_info_u2081_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
        return v___x_4631_;
    } else {
        let mut v_changesAfter_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_changesAfter_4632_ = crate::leanh::lean_ctor_get(v_diff_4621_, 1);
        crate::leanh::lean_inc(v_changesAfter_4632_);
        crate::leanh::lean_dec_ref(v_diff_4621_);
        v___x_4633_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_4629_, v_changesAfter_4632_, v_info_u2081_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
        return v___x_4633_;
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(
    mut v_useAfter_4634_: *mut crate::leanh::LeanObject,
    mut v_diff_4635_: *mut crate::leanh::LeanObject,
    mut v_info_u2081_4636_: *mut crate::leanh::LeanObject,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_a_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_4642_: u8 = 0;
    let mut v_res_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4642_ = (crate::leanh::lean_unbox(v_useAfter_4634_) as u8);
    v_res_4643_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
        v_useAfter_boxed_4642_,
        v_diff_4635_,
        v_info_u2081_4636_,
        v_a_4637_,
        v_a_4638_,
        v_a_4639_,
        v_a_4640_,
    );
    crate::leanh::lean_dec(v_a_4640_);
    crate::leanh::lean_dec_ref(v_a_4639_);
    crate::leanh::lean_dec(v_a_4638_);
    crate::leanh::lean_dec_ref(v_a_4637_);
    return v_res_4643_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(
    mut v_00_u03b1_4644_: *mut crate::leanh::LeanObject,
    mut v_merger_4645_: *mut crate::leanh::LeanObject,
    mut v_pm_4646_: *mut crate::leanh::LeanObject,
    mut v_tt_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4653_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_4645_, v_pm_4646_, v_tt_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
    return v___x_4653_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(
    mut v_00_u03b1_4654_: *mut crate::leanh::LeanObject,
    mut v_merger_4655_: *mut crate::leanh::LeanObject,
    mut v_pm_4656_: *mut crate::leanh::LeanObject,
    mut v_tt_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4663_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_4654_, v_merger_4655_, v_pm_4656_, v_tt_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
    crate::leanh::lean_dec(v___y_4661_);
    crate::leanh::lean_dec_ref(v___y_4660_);
    crate::leanh::lean_dec(v___y_4659_);
    crate::leanh::lean_dec_ref(v___y_4658_);
    return v_res_4663_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(
    mut v_00_u03b4_4664_: *mut crate::leanh::LeanObject,
    mut v_t_4665_: *mut crate::leanh::LeanObject,
    mut v_k_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_4665_, v_k_4666_);
    return v___x_4667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(
    mut v_00_u03b4_4668_: *mut crate::leanh::LeanObject,
    mut v_t_4669_: *mut crate::leanh::LeanObject,
    mut v_k_4670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_4668_, v_t_4669_, v_k_4670_);
    crate::leanh::lean_dec(v_k_4670_);
    crate::leanh::lean_dec(v_t_4669_);
    return v_res_4671_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(
    mut v_00_u03b1_4672_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4673_: *mut crate::leanh::LeanObject,
    mut v_f_4674_: *mut crate::leanh::LeanObject,
    mut v_x_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
    mut v___y_4678_: *mut crate::leanh::LeanObject,
    mut v___y_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4674_, v_x_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
    return v___x_4681_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(
    mut v_00_u03b1_4682_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4683_: *mut crate::leanh::LeanObject,
    mut v_f_4684_: *mut crate::leanh::LeanObject,
    mut v_x_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_4682_, v_00_u03b2_4683_, v_f_4684_, v_x_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
    crate::leanh::lean_dec(v___y_4689_);
    crate::leanh::lean_dec_ref(v___y_4688_);
    crate::leanh::lean_dec(v___y_4687_);
    crate::leanh::lean_dec_ref(v___y_4686_);
    return v_res_4691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4692_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4693_: *mut crate::leanh::LeanObject,
    mut v_f_4694_: *mut crate::leanh::LeanObject,
    mut v_sz_4695_: usize,
    mut v_i_4696_: usize,
    mut v_bs_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4694_, v_sz_4695_, v_i_4696_, v_bs_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
    return v___x_4703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4704_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4705_: *mut crate::leanh::LeanObject,
    mut v_f_4706_: *mut crate::leanh::LeanObject,
    mut v_sz_4707_: *mut crate::leanh::LeanObject,
    mut v_i_4708_: *mut crate::leanh::LeanObject,
    mut v_bs_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
    mut v___y_4714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4715_: usize = 0;
    let mut v_i_boxed_4716_: usize = 0;
    let mut v_res_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4715_ = crate::leanh::lean_unbox_usize(v_sz_4707_);
    crate::leanh::lean_dec(v_sz_4707_);
    v_i_boxed_4716_ = crate::leanh::lean_unbox_usize(v_i_4708_);
    crate::leanh::lean_dec(v_i_4708_);
    v_res_4717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_4704_, v_00_u03b2_4705_, v_f_4706_, v_sz_boxed_4715_, v_i_boxed_4716_, v_bs_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
    crate::leanh::lean_dec(v___y_4713_);
    crate::leanh::lean_dec_ref(v___y_4712_);
    crate::leanh::lean_dec(v___y_4711_);
    crate::leanh::lean_dec_ref(v___y_4710_);
    return v_res_4717_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(
    mut v_e_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4721_ = l_Lean_Expr_hasMVar(v_e_4718_);
                if v___x_4721_ == 0 {
                    v___x_4722_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4722_, 0, v_e_4718_);
                    return v___x_4722_;
                } else {
                    v___x_4723_ = lean_st_ref_get(v___y_4719_);
                    v_mctx_4724_ = crate::leanh::lean_ctor_get(v___x_4723_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4724_);
                    crate::leanh::lean_dec(v___x_4723_);
                    v___x_4725_ = l_Lean_instantiateMVarsCore(v_mctx_4724_, v_e_4718_);
                    v_fst_4726_ = crate::leanh::lean_ctor_get(v___x_4725_, 0);
                    crate::leanh::lean_inc(v_fst_4726_);
                    v_snd_4727_ = crate::leanh::lean_ctor_get(v___x_4725_, 1);
                    crate::leanh::lean_inc(v_snd_4727_);
                    crate::leanh::lean_dec_ref(v___x_4725_);
                    v___x_4728_ = lean_st_ref_take(v___y_4719_);
                    v_cache_4729_ = crate::leanh::lean_ctor_get(v___x_4728_, 1);
                    v_zetaDeltaFVarIds_4730_ = crate::leanh::lean_ctor_get(v___x_4728_, 2);
                    v_postponed_4731_ = crate::leanh::lean_ctor_get(v___x_4728_, 3);
                    v_diag_4732_ = crate::leanh::lean_ctor_get(v___x_4728_, 4);
                    v_isSharedCheck_4741_ = (!crate::leanh::lean_is_exclusive(v___x_4728_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v_unused_4742_ = crate::leanh::lean_ctor_get(v___x_4728_, 0);
                        crate::leanh::lean_dec(v_unused_4742_);
                        v___x_4734_ = v___x_4728_;
                        v_isShared_4735_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4732_);
                        crate::leanh::lean_inc(v_postponed_4731_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4730_);
                        crate::leanh::lean_inc(v_cache_4729_);
                        crate::leanh::lean_dec(v___x_4728_);
                        v___x_4734_ = crate::leanh::lean_box(0);
                        v_isShared_4735_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4734_, 0, v_snd_4727_);
                    v___x_4737_ = v___x_4734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_snd_4727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_cache_4729_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4740_,
                        2,
                        v_zetaDeltaFVarIds_4730_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 3, v_postponed_4731_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 4, v_diag_4732_);
                    v___x_4737_ = v_reuseFailAlloc_4740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4738_ = lean_st_ref_set(v___y_4719_, v___x_4737_);
                v___x_4739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4739_, 0, v_fst_4726_);
                return v___x_4739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(
    mut v_e_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_4743_, v___y_4744_);
    crate::leanh::lean_dec(v___y_4744_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(
    mut v_e_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4753_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_4747_, v___y_4749_);
    return v___x_4753_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(
    mut v_e_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4760_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
    crate::leanh::lean_dec(v___y_4758_);
    crate::leanh::lean_dec_ref(v___y_4757_);
    crate::leanh::lean_dec(v___y_4756_);
    crate::leanh::lean_dec_ref(v___y_4755_);
    return v_res_4760_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4762_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0;
    v___x_4763_ = l_Lean_stringToMessageData(v___x_4762_);
    return v___x_4763_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(
    mut v_useAfter_4764_: u8,
    mut v_t_u2080_4765_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
    mut v_a_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_names_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___y_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_a_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_a_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4772_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 0);
                v_fvarIds_4773_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 1);
                v_type_4774_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 2);
                v_val_x3f_4775_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 3);
                v_isInstance_x3f_4776_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 4);
                v_isType_x3f_4777_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 5);
                v_isInserted_x3f_4778_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 6);
                v_isRemoved_x3f_4779_ = crate::leanh::lean_ctor_get(v_h_u2081_4766_, 7);
                v_isSharedCheck_4834_ = (!crate::leanh::lean_is_exclusive(v_h_u2081_4766_)) as u8;
                if v_isSharedCheck_4834_ == 0 {
                    v___x_4781_ = v_h_u2081_4766_;
                    v_isShared_4782_ = v_isSharedCheck_4834_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isRemoved_x3f_4779_);
                    crate::leanh::lean_inc(v_isInserted_x3f_4778_);
                    crate::leanh::lean_inc(v_isType_x3f_4777_);
                    crate::leanh::lean_inc(v_isInstance_x3f_4776_);
                    crate::leanh::lean_inc(v_val_x3f_4775_);
                    crate::leanh::lean_inc(v_type_4774_);
                    crate::leanh::lean_inc(v_fvarIds_4773_);
                    crate::leanh::lean_inc(v_names_4772_);
                    crate::leanh::lean_dec(v_h_u2081_4766_);
                    v___x_4781_ = crate::leanh::lean_box(0);
                    v_isShared_4782_ = v_isSharedCheck_4834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4824_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4825_ = lean_array_get_size(v_fvarIds_4773_);
                v___x_4826_ = lean_nat_dec_lt(v___x_4824_, v___x_4825_);
                if v___x_4826_ == 0 {
                    crate::leanh::lean_del_object(v___x_4781_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4779_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4778_);
                    crate::leanh::lean_dec(v_isType_x3f_4777_);
                    crate::leanh::lean_dec(v_isInstance_x3f_4776_);
                    crate::leanh::lean_dec(v_val_x3f_4775_);
                    crate::leanh::lean_dec_ref(v_type_4774_);
                    crate::leanh::lean_dec_ref(v_fvarIds_4773_);
                    crate::leanh::lean_dec_ref(v_names_4772_);
                    crate::leanh::lean_dec_ref(v_t_u2080_4765_);
                    v___x_4827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
                    v___x_4828_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_4827_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                    return v___x_4828_;
                } else {
                    v___x_4829_ = lean_array_fget_borrowed(v_fvarIds_4773_, v___x_4824_);
                    crate::leanh::lean_inc(v___x_4829_);
                    v___x_4830_ = l_Lean_Expr_fvar___override(v___x_4829_);
                    crate::leanh::lean_inc(v_a_4770_);
                    crate::leanh::lean_inc_ref(v_a_4769_);
                    crate::leanh::lean_inc(v_a_4768_);
                    crate::leanh::lean_inc_ref(v_a_4767_);
                    v___x_4831_ =
                        lean_infer_type(v___x_4830_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                    if crate::leanh::lean_obj_tag(v___x_4831_) == 0 {
                        v_a_4832_ = crate::leanh::lean_ctor_get(v___x_4831_, 0);
                        crate::leanh::lean_inc(v_a_4832_);
                        crate::leanh::lean_dec_ref_known(v___x_4831_, 1);
                        v___x_4833_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_4832_, v_a_4768_);
                        v___y_4784_ = v___x_4833_;
                        state = 2;
                        continue;
                    } else {
                        v___y_4784_ = v___x_4831_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4784_) == 0 {
                    v_a_4785_ = crate::leanh::lean_ctor_get(v___y_4784_, 0);
                    crate::leanh::lean_inc(v_a_4785_);
                    crate::leanh::lean_dec_ref_known(v___y_4784_, 1);
                    v___x_4786_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
                        v_t_u2080_4765_,
                        v_a_4785_,
                        v_useAfter_4764_,
                        v_a_4767_,
                        v_a_4768_,
                        v_a_4769_,
                        v_a_4770_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4786_) == 0 {
                        v_a_4787_ = crate::leanh::lean_ctor_get(v___x_4786_, 0);
                        crate::leanh::lean_inc(v_a_4787_);
                        crate::leanh::lean_dec_ref_known(v___x_4786_, 1);
                        v___x_4788_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
                            v_useAfter_4764_,
                            v_a_4787_,
                            v_type_4774_,
                            v_a_4767_,
                            v_a_4768_,
                            v_a_4769_,
                            v_a_4770_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4788_) == 0 {
                            v_a_4789_ = crate::leanh::lean_ctor_get(v___x_4788_, 0);
                            v_isSharedCheck_4799_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4788_)) as u8;
                            if v_isSharedCheck_4799_ == 0 {
                                v___x_4791_ = v___x_4788_;
                                v_isShared_4792_ = v_isSharedCheck_4799_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4789_);
                                crate::leanh::lean_dec(v___x_4788_);
                                v___x_4791_ = crate::leanh::lean_box(0);
                                v_isShared_4792_ = v_isSharedCheck_4799_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4781_);
                            crate::leanh::lean_dec(v_isRemoved_x3f_4779_);
                            crate::leanh::lean_dec(v_isInserted_x3f_4778_);
                            crate::leanh::lean_dec(v_isType_x3f_4777_);
                            crate::leanh::lean_dec(v_isInstance_x3f_4776_);
                            crate::leanh::lean_dec(v_val_x3f_4775_);
                            crate::leanh::lean_dec_ref(v_fvarIds_4773_);
                            crate::leanh::lean_dec_ref(v_names_4772_);
                            v_a_4800_ = crate::leanh::lean_ctor_get(v___x_4788_, 0);
                            v_isSharedCheck_4807_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4788_)) as u8;
                            if v_isSharedCheck_4807_ == 0 {
                                v___x_4802_ = v___x_4788_;
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4800_);
                                crate::leanh::lean_dec(v___x_4788_);
                                v___x_4802_ = crate::leanh::lean_box(0);
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4781_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_4779_);
                        crate::leanh::lean_dec(v_isInserted_x3f_4778_);
                        crate::leanh::lean_dec(v_isType_x3f_4777_);
                        crate::leanh::lean_dec(v_isInstance_x3f_4776_);
                        crate::leanh::lean_dec(v_val_x3f_4775_);
                        crate::leanh::lean_dec_ref(v_type_4774_);
                        crate::leanh::lean_dec_ref(v_fvarIds_4773_);
                        crate::leanh::lean_dec_ref(v_names_4772_);
                        v_a_4808_ = crate::leanh::lean_ctor_get(v___x_4786_, 0);
                        v_isSharedCheck_4815_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4786_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v___x_4810_ = v___x_4786_;
                            v_isShared_4811_ = v_isSharedCheck_4815_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4808_);
                            crate::leanh::lean_dec(v___x_4786_);
                            v___x_4810_ = crate::leanh::lean_box(0);
                            v_isShared_4811_ = v_isSharedCheck_4815_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4781_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4779_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4778_);
                    crate::leanh::lean_dec(v_isType_x3f_4777_);
                    crate::leanh::lean_dec(v_isInstance_x3f_4776_);
                    crate::leanh::lean_dec(v_val_x3f_4775_);
                    crate::leanh::lean_dec_ref(v_type_4774_);
                    crate::leanh::lean_dec_ref(v_fvarIds_4773_);
                    crate::leanh::lean_dec_ref(v_names_4772_);
                    crate::leanh::lean_dec_ref(v_t_u2080_4765_);
                    v_a_4816_ = crate::leanh::lean_ctor_get(v___y_4784_, 0);
                    v_isSharedCheck_4823_ = (!crate::leanh::lean_is_exclusive(v___y_4784_)) as u8;
                    if v_isSharedCheck_4823_ == 0 {
                        v___x_4818_ = v___y_4784_;
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4816_);
                        crate::leanh::lean_dec(v___y_4784_);
                        v___x_4818_ = crate::leanh::lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4781_, 2, v_a_4789_);
                    v___x_4794_ = v___x_4781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_names_4772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_fvarIds_4773_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_a_4789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 3, v_val_x3f_4775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 4, v_isInstance_x3f_4776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 5, v_isType_x3f_4777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 6, v_isInserted_x3f_4778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 7, v_isRemoved_x3f_4779_);
                    v___x_4794_ = v_reuseFailAlloc_4798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4791_, 0, v___x_4794_);
                    v___x_4796_ = v___x_4791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4796_;
            }
            6 => {
                if v_isShared_4803_ == 0 {
                    v___x_4805_ = v___x_4802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4805_;
            }
            8 => {
                if v_isShared_4811_ == 0 {
                    v___x_4813_ = v___x_4810_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
                    v___x_4813_ = v_reuseFailAlloc_4814_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4813_;
            }
            10 => {
                if v_isShared_4819_ == 0 {
                    v___x_4821_ = v___x_4818_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___boxed(
    mut v_useAfter_4835_: *mut crate::leanh::LeanObject,
    mut v_t_u2080_4836_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4837_: *mut crate::leanh::LeanObject,
    mut v_a_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
    mut v_a_4840_: *mut crate::leanh::LeanObject,
    mut v_a_4841_: *mut crate::leanh::LeanObject,
    mut v_a_4842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_4843_: u8 = 0;
    let mut v_res_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4843_ = (crate::leanh::lean_unbox(v_useAfter_4835_) as u8);
    v_res_4844_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(
        v_useAfter_boxed_4843_,
        v_t_u2080_4836_,
        v_h_u2081_4837_,
        v_a_4838_,
        v_a_4839_,
        v_a_4840_,
        v_a_4841_,
    );
    crate::leanh::lean_dec(v_a_4841_);
    crate::leanh::lean_dec_ref(v_a_4840_);
    crate::leanh::lean_dec(v_a_4839_);
    crate::leanh::lean_dec_ref(v_a_4838_);
    return v_res_4844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(
    mut v_ctx_u2080_4848_: *mut crate::leanh::LeanObject,
    mut v_useAfter_4849_: u8,
    mut v_h_u2081_4850_: *mut crate::leanh::LeanObject,
    mut v___x_4851_: *mut crate::leanh::LeanObject,
    mut v___x_4852_: *mut crate::leanh::LeanObject,
    mut v_as_4853_: *mut crate::leanh::LeanObject,
    mut v_sz_4854_: usize,
    mut v_i_4855_: usize,
    mut v_b_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4886_: u8 = 0;
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut v_a_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_a_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_type_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4921_: u8 = 0;
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut v_unused_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v_unused_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: usize = 0;
    let mut v___x_4960_: usize = 0;
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4862_ = lean_usize_dec_lt(v_i_4855_, v_sz_4854_);
                if v___x_4862_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4852_);
                    crate::leanh::lean_dec_ref(v___x_4851_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4850_);
                    v___x_4863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4863_, 0, v_b_4856_);
                    return v___x_4863_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4856_);
                    v_a_4864_ = lean_array_uget(v_as_4853_, v_i_4855_);
                    v_fst_4865_ = crate::leanh::lean_ctor_get(v_a_4864_, 0);
                    v_snd_4866_ = crate::leanh::lean_ctor_get(v_a_4864_, 1);
                    v_isSharedCheck_4962_ = (!crate::leanh::lean_is_exclusive(v_a_4864_)) as u8;
                    if v_isSharedCheck_4962_ == 0 {
                        v___x_4868_ = v_a_4864_;
                        v_isShared_4869_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4866_);
                        crate::leanh::lean_inc(v_fst_4865_);
                        crate::leanh::lean_dec(v_a_4864_);
                        v___x_4868_ = crate::leanh::lean_box(0);
                        v_isShared_4869_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4870_ = crate::leanh::lean_box(0);
                v___x_4871_ = l_Lean_LocalContext_contains(v_ctx_u2080_4848_, v_snd_4866_);
                crate::leanh::lean_dec(v_snd_4866_);
                if v___x_4871_ == 0 {
                    v___x_4872_ = crate::leanh::lean_box(0);
                    v___x_4873_ = l_Lean_Name_str___override(v___x_4872_, v_fst_4865_);
                    v___x_4874_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_4848_, v___x_4873_);
                    crate::leanh::lean_dec(v___x_4873_);
                    if crate::leanh::lean_obj_tag(v___x_4874_) == 1 {
                        crate::leanh::lean_dec_ref(v___x_4852_);
                        crate::leanh::lean_dec_ref(v___x_4851_);
                        v_val_4875_ = crate::leanh::lean_ctor_get(v___x_4874_, 0);
                        v_isSharedCheck_4913_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4874_)) as u8;
                        if v_isSharedCheck_4913_ == 0 {
                            v___x_4877_ = v___x_4874_;
                            v_isShared_4878_ = v_isSharedCheck_4913_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4875_);
                            crate::leanh::lean_dec(v___x_4874_);
                            v___x_4877_ = crate::leanh::lean_box(0);
                            v_isShared_4878_ = v_isSharedCheck_4913_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4874_);
                        if v_useAfter_4849_ == 0 {
                            v_type_4914_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 2);
                            v_val_x3f_4915_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 3);
                            v_isInstance_x3f_4916_ =
                                crate::leanh::lean_ctor_get(v_h_u2081_4850_, 4);
                            v_isType_x3f_4917_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 5);
                            v_isInserted_x3f_4918_ =
                                crate::leanh::lean_ctor_get(v_h_u2081_4850_, 6);
                            v_isSharedCheck_4932_ =
                                (!crate::leanh::lean_is_exclusive(v_h_u2081_4850_)) as u8;
                            if v_isSharedCheck_4932_ == 0 {
                                v_unused_4933_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 7);
                                crate::leanh::lean_dec(v_unused_4933_);
                                v_unused_4934_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 1);
                                crate::leanh::lean_dec(v_unused_4934_);
                                v_unused_4935_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 0);
                                crate::leanh::lean_dec(v_unused_4935_);
                                v___x_4920_ = v_h_u2081_4850_;
                                v_isShared_4921_ = v_isSharedCheck_4932_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_isInserted_x3f_4918_);
                                crate::leanh::lean_inc(v_isType_x3f_4917_);
                                crate::leanh::lean_inc(v_isInstance_x3f_4916_);
                                crate::leanh::lean_inc(v_val_x3f_4915_);
                                crate::leanh::lean_inc(v_type_4914_);
                                crate::leanh::lean_dec(v_h_u2081_4850_);
                                v___x_4920_ = crate::leanh::lean_box(0);
                                v_isShared_4921_ = v_isSharedCheck_4932_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v_type_4936_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 2);
                            v_val_x3f_4937_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 3);
                            v_isInstance_x3f_4938_ =
                                crate::leanh::lean_ctor_get(v_h_u2081_4850_, 4);
                            v_isType_x3f_4939_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 5);
                            v_isRemoved_x3f_4940_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 7);
                            v_isSharedCheck_4954_ =
                                (!crate::leanh::lean_is_exclusive(v_h_u2081_4850_)) as u8;
                            if v_isSharedCheck_4954_ == 0 {
                                v_unused_4955_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 6);
                                crate::leanh::lean_dec(v_unused_4955_);
                                v_unused_4956_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 1);
                                crate::leanh::lean_dec(v_unused_4956_);
                                v_unused_4957_ = crate::leanh::lean_ctor_get(v_h_u2081_4850_, 0);
                                crate::leanh::lean_dec(v_unused_4957_);
                                v___x_4942_ = v_h_u2081_4850_;
                                v_isShared_4943_ = v_isSharedCheck_4954_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_isRemoved_x3f_4940_);
                                crate::leanh::lean_inc(v_isType_x3f_4939_);
                                crate::leanh::lean_inc(v_isInstance_x3f_4938_);
                                crate::leanh::lean_inc(v_val_x3f_4937_);
                                crate::leanh::lean_inc(v_type_4936_);
                                crate::leanh::lean_dec(v_h_u2081_4850_);
                                v___x_4942_ = crate::leanh::lean_box(0);
                                v_isShared_4943_ = v_isSharedCheck_4954_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4868_);
                    crate::leanh::lean_dec(v_fst_4865_);
                    v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0;
                    v___x_4959_ = 1usize;
                    v___x_4960_ = lean_usize_add(v_i_4855_, v___x_4959_);
                    v_i_4855_ = v___x_4960_;
                    v_b_4856_ = v___x_4958_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_4879_ = l_Lean_LocalDecl_type(v_val_4875_);
                crate::leanh::lean_dec(v_val_4875_);
                v___x_4880_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_4879_, v___y_4858_);
                if crate::leanh::lean_obj_tag(v___x_4880_) == 0 {
                    v_a_4881_ = crate::leanh::lean_ctor_get(v___x_4880_, 0);
                    crate::leanh::lean_inc(v_a_4881_);
                    crate::leanh::lean_dec_ref_known(v___x_4880_, 1);
                    v___x_4882_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_4849_, v_a_4881_, v_h_u2081_4850_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
                    if crate::leanh::lean_obj_tag(v___x_4882_) == 0 {
                        v_a_4883_ = crate::leanh::lean_ctor_get(v___x_4882_, 0);
                        v_isSharedCheck_4896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4882_)) as u8;
                        if v_isSharedCheck_4896_ == 0 {
                            v___x_4885_ = v___x_4882_;
                            v_isShared_4886_ = v_isSharedCheck_4896_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4883_);
                            crate::leanh::lean_dec(v___x_4882_);
                            v___x_4885_ = crate::leanh::lean_box(0);
                            v_isShared_4886_ = v_isSharedCheck_4896_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4877_);
                        crate::leanh::lean_del_object(v___x_4868_);
                        v_a_4897_ = crate::leanh::lean_ctor_get(v___x_4882_, 0);
                        v_isSharedCheck_4904_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4882_)) as u8;
                        if v_isSharedCheck_4904_ == 0 {
                            v___x_4899_ = v___x_4882_;
                            v_isShared_4900_ = v_isSharedCheck_4904_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4897_);
                            crate::leanh::lean_dec(v___x_4882_);
                            v___x_4899_ = crate::leanh::lean_box(0);
                            v_isShared_4900_ = v_isSharedCheck_4904_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4877_);
                    crate::leanh::lean_del_object(v___x_4868_);
                    crate::leanh::lean_dec_ref(v_h_u2081_4850_);
                    v_a_4905_ = crate::leanh::lean_ctor_get(v___x_4880_, 0);
                    v_isSharedCheck_4912_ = (!crate::leanh::lean_is_exclusive(v___x_4880_)) as u8;
                    if v_isSharedCheck_4912_ == 0 {
                        v___x_4907_ = v___x_4880_;
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4905_);
                        crate::leanh::lean_dec(v___x_4880_);
                        v___x_4907_ = crate::leanh::lean_box(0);
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4878_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4877_, 0, v_a_4883_);
                    v___x_4888_ = v___x_4877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4883_);
                    v___x_4888_ = v_reuseFailAlloc_4895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4868_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4894_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4870_);
                    v___x_4890_ = v_reuseFailAlloc_4894_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4885_, 0, v___x_4890_);
                    v___x_4892_ = v___x_4885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
                    v___x_4892_ = v_reuseFailAlloc_4893_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4892_;
            }
            7 => {
                if v_isShared_4900_ == 0 {
                    v___x_4902_ = v___x_4899_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
                    v___x_4902_ = v_reuseFailAlloc_4903_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4902_;
            }
            9 => {
                if v_isShared_4908_ == 0 {
                    v___x_4910_ = v___x_4907_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4910_;
            }
            11 => {
                v___x_4922_ = crate::leanh::lean_box((v___x_4862_) as usize);
                v___x_4923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4922_);
                if v_isShared_4921_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4920_, 7, v___x_4923_);
                    crate::leanh::lean_ctor_set(v___x_4920_, 1, v___x_4852_);
                    crate::leanh::lean_ctor_set(v___x_4920_, 0, v___x_4851_);
                    v___x_4925_ = v___x_4920_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4931_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 1, v___x_4852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_type_4914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_val_x3f_4915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 4, v_isInstance_x3f_4916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 5, v_isType_x3f_4917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 6, v_isInserted_x3f_4918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 7, v___x_4923_);
                    v___x_4925_ = v_reuseFailAlloc_4931_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4926_, 0, v___x_4925_);
                if v_isShared_4869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4926_);
                    v___x_4928_ = v___x_4868_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___x_4870_);
                    v___x_4928_ = v_reuseFailAlloc_4930_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4929_, 0, v___x_4928_);
                return v___x_4929_;
            }
            14 => {
                v___x_4944_ = crate::leanh::lean_box((v___x_4862_) as usize);
                v___x_4945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4945_, 0, v___x_4944_);
                if v_isShared_4943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4942_, 6, v___x_4945_);
                    crate::leanh::lean_ctor_set(v___x_4942_, 1, v___x_4852_);
                    crate::leanh::lean_ctor_set(v___x_4942_, 0, v___x_4851_);
                    v___x_4947_ = v___x_4942_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4953_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 1, v___x_4852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_type_4936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_val_x3f_4937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 4, v_isInstance_x3f_4938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 5, v_isType_x3f_4939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 6, v___x_4945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 7, v_isRemoved_x3f_4940_);
                    v___x_4947_ = v_reuseFailAlloc_4953_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4948_, 0, v___x_4947_);
                if v_isShared_4869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4948_);
                    v___x_4950_ = v___x_4868_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 1, v___x_4870_);
                    v___x_4950_ = v_reuseFailAlloc_4952_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4951_, 0, v___x_4950_);
                return v___x_4951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(
    mut v_ctx_u2080_4963_: *mut crate::leanh::LeanObject,
    mut v_useAfter_4964_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4965_: *mut crate::leanh::LeanObject,
    mut v___x_4966_: *mut crate::leanh::LeanObject,
    mut v___x_4967_: *mut crate::leanh::LeanObject,
    mut v_as_4968_: *mut crate::leanh::LeanObject,
    mut v_sz_4969_: *mut crate::leanh::LeanObject,
    mut v_i_4970_: *mut crate::leanh::LeanObject,
    mut v_b_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_4977_: u8 = 0;
    let mut v_sz_boxed_4978_: usize = 0;
    let mut v_i_boxed_4979_: usize = 0;
    let mut v_res_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4977_ = (crate::leanh::lean_unbox(v_useAfter_4964_) as u8);
    v_sz_boxed_4978_ = crate::leanh::lean_unbox_usize(v_sz_4969_);
    crate::leanh::lean_dec(v_sz_4969_);
    v_i_boxed_4979_ = crate::leanh::lean_unbox_usize(v_i_4970_);
    crate::leanh::lean_dec(v_i_4970_);
    v_res_4980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_4963_, v_useAfter_boxed_4977_, v_h_u2081_4965_, v___x_4966_, v___x_4967_, v_as_4968_, v_sz_boxed_4978_, v_i_boxed_4979_, v_b_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
    crate::leanh::lean_dec(v___y_4975_);
    crate::leanh::lean_dec_ref(v___y_4974_);
    crate::leanh::lean_dec(v___y_4973_);
    crate::leanh::lean_dec_ref(v___y_4972_);
    crate::leanh::lean_dec_ref(v_as_4968_);
    crate::leanh::lean_dec_ref(v_ctx_u2080_4963_);
    return v_res_4980_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
    mut v_useAfter_4981_: u8,
    mut v_ctx_u2080_4982_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_4983_: *mut crate::leanh::LeanObject,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
    mut v_a_4985_: *mut crate::leanh::LeanObject,
    mut v_a_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_names_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4993_: usize = 0;
    let mut v___x_4994_: usize = 0;
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4999_: u8 = 0;
    let mut v_fst_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_a_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4989_ = crate::leanh::lean_ctor_get(v_h_u2081_4983_, 0);
                v_fvarIds_4990_ = crate::leanh::lean_ctor_get(v_h_u2081_4983_, 1);
                v___x_4991_ = l_Array_zip___redArg(v_names_4989_, v_fvarIds_4990_);
                v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0;
                v_sz_4993_ = lean_array_size(v___x_4991_);
                v___x_4994_ = 0usize;
                crate::leanh::lean_inc_ref(v_fvarIds_4990_);
                crate::leanh::lean_inc_ref(v_names_4989_);
                crate::leanh::lean_inc_ref(v_h_u2081_4983_);
                v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_4982_, v_useAfter_4981_, v_h_u2081_4983_, v_names_4989_, v_fvarIds_4990_, v___x_4991_, v_sz_4993_, v___x_4994_, v___x_4992_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
                crate::leanh::lean_dec_ref(v___x_4991_);
                if crate::leanh::lean_obj_tag(v___x_4995_) == 0 {
                    v_a_4996_ = crate::leanh::lean_ctor_get(v___x_4995_, 0);
                    v_isSharedCheck_5008_ = (!crate::leanh::lean_is_exclusive(v___x_4995_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v___x_4998_ = v___x_4995_;
                        v_isShared_4999_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4996_);
                        crate::leanh::lean_dec(v___x_4995_);
                        v___x_4998_ = crate::leanh::lean_box(0);
                        v_isShared_4999_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2081_4983_);
                    v_a_5009_ = crate::leanh::lean_ctor_get(v___x_4995_, 0);
                    v_isSharedCheck_5016_ = (!crate::leanh::lean_is_exclusive(v___x_4995_)) as u8;
                    if v_isSharedCheck_5016_ == 0 {
                        v___x_5011_ = v___x_4995_;
                        v_isShared_5012_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5009_);
                        crate::leanh::lean_dec(v___x_4995_);
                        v___x_5011_ = crate::leanh::lean_box(0);
                        v_isShared_5012_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5000_ = crate::leanh::lean_ctor_get(v_a_4996_, 0);
                crate::leanh::lean_inc(v_fst_5000_);
                crate::leanh::lean_dec(v_a_4996_);
                if crate::leanh::lean_obj_tag(v_fst_5000_) == 0 {
                    if v_isShared_4999_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4998_, 0, v_h_u2081_4983_);
                        v___x_5002_ = v___x_4998_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_h_u2081_4983_);
                        v___x_5002_ = v_reuseFailAlloc_5003_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_u2081_4983_);
                    v_val_5004_ = crate::leanh::lean_ctor_get(v_fst_5000_, 0);
                    crate::leanh::lean_inc(v_val_5004_);
                    crate::leanh::lean_dec_ref_known(v_fst_5000_, 1);
                    if v_isShared_4999_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4998_, 0, v_val_5004_);
                        v___x_5006_ = v___x_4998_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_val_5004_);
                        v___x_5006_ = v_reuseFailAlloc_5007_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5002_;
            }
            3 => {
                return v___x_5006_;
            }
            4 => {
                if v_isShared_5012_ == 0 {
                    v___x_5014_ = v___x_5011_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
                    v___x_5014_ = v_reuseFailAlloc_5015_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle___boxed(
    mut v_useAfter_5017_: *mut crate::leanh::LeanObject,
    mut v_ctx_u2080_5018_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_5019_: *mut crate::leanh::LeanObject,
    mut v_a_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v_a_5022_: *mut crate::leanh::LeanObject,
    mut v_a_5023_: *mut crate::leanh::LeanObject,
    mut v_a_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_5025_: u8 = 0;
    let mut v_res_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5025_ = (crate::leanh::lean_unbox(v_useAfter_5017_) as u8);
    v_res_5026_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
        v_useAfter_boxed_5025_,
        v_ctx_u2080_5018_,
        v_h_u2081_5019_,
        v_a_5020_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
    );
    crate::leanh::lean_dec(v_a_5023_);
    crate::leanh::lean_dec_ref(v_a_5022_);
    crate::leanh::lean_dec(v_a_5021_);
    crate::leanh::lean_dec_ref(v_a_5020_);
    crate::leanh::lean_dec_ref(v_ctx_u2080_5018_);
    return v_res_5026_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(
    mut v_useAfter_5027_: u8,
    mut v_lctx_u2080_5028_: *mut crate::leanh::LeanObject,
    mut v_sz_5029_: usize,
    mut v_i_5030_: usize,
    mut v_bs_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: usize = 0;
    let mut v___x_5045_: usize = 0;
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5037_ = lean_usize_dec_lt(v_i_5030_, v_sz_5029_);
                if v___x_5037_ == 0 {
                    v___x_5038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5038_, 0, v_bs_5031_);
                    return v___x_5038_;
                } else {
                    v_v_5039_ = lean_array_uget_borrowed(v_bs_5031_, v_i_5030_);
                    crate::leanh::lean_inc(v_v_5039_);
                    v___x_5040_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
                        v_useAfter_5027_,
                        v_lctx_u2080_5028_,
                        v_v_5039_,
                        v___y_5032_,
                        v___y_5033_,
                        v___y_5034_,
                        v___y_5035_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5040_) == 0 {
                        v_a_5041_ = crate::leanh::lean_ctor_get(v___x_5040_, 0);
                        crate::leanh::lean_inc(v_a_5041_);
                        crate::leanh::lean_dec_ref_known(v___x_5040_, 1);
                        v___x_5042_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5043_ = lean_array_uset(v_bs_5031_, v_i_5030_, v___x_5042_);
                        v___x_5044_ = 1usize;
                        v___x_5045_ = lean_usize_add(v_i_5030_, v___x_5044_);
                        v___x_5046_ = lean_array_uset(v_bs_x27_5043_, v_i_5030_, v_a_5041_);
                        v_i_5030_ = v___x_5045_;
                        v_bs_5031_ = v___x_5046_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5031_);
                        v_a_5048_ = crate::leanh::lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5055_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5055_ == 0 {
                            v___x_5050_ = v___x_5040_;
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5048_);
                            crate::leanh::lean_dec(v___x_5040_);
                            v___x_5050_ = crate::leanh::lean_box(0);
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5051_ == 0 {
                    v___x_5053_ = v___x_5050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
                    v___x_5053_ = v_reuseFailAlloc_5054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0___boxed(
    mut v_useAfter_5056_: *mut crate::leanh::LeanObject,
    mut v_lctx_u2080_5057_: *mut crate::leanh::LeanObject,
    mut v_sz_5058_: *mut crate::leanh::LeanObject,
    mut v_i_5059_: *mut crate::leanh::LeanObject,
    mut v_bs_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_5066_: u8 = 0;
    let mut v_sz_boxed_5067_: usize = 0;
    let mut v_i_boxed_5068_: usize = 0;
    let mut v_res_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5066_ = (crate::leanh::lean_unbox(v_useAfter_5056_) as u8);
    v_sz_boxed_5067_ = crate::leanh::lean_unbox_usize(v_sz_5058_);
    crate::leanh::lean_dec(v_sz_5058_);
    v_i_boxed_5068_ = crate::leanh::lean_unbox_usize(v_i_5059_);
    crate::leanh::lean_dec(v_i_5059_);
    v_res_5069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_5066_, v_lctx_u2080_5057_, v_sz_boxed_5067_, v_i_boxed_5068_, v_bs_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
    crate::leanh::lean_dec(v___y_5064_);
    crate::leanh::lean_dec_ref(v___y_5063_);
    crate::leanh::lean_dec(v___y_5062_);
    crate::leanh::lean_dec_ref(v___y_5061_);
    crate::leanh::lean_dec_ref(v_lctx_u2080_5057_);
    return v_res_5069_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(
    mut v_useAfter_5070_: u8,
    mut v_lctx_u2080_5071_: *mut crate::leanh::LeanObject,
    mut v_hs_u2081_5072_: *mut crate::leanh::LeanObject,
    mut v_a_5073_: *mut crate::leanh::LeanObject,
    mut v_a_5074_: *mut crate::leanh::LeanObject,
    mut v_a_5075_: *mut crate::leanh::LeanObject,
    mut v_a_5076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5078_: usize = 0;
    let mut v___x_5079_: usize = 0;
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_5078_ = lean_array_size(v_hs_u2081_5072_);
    v___x_5079_ = 0usize;
    v___x_5080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_5070_, v_lctx_u2080_5071_, v_sz_5078_, v___x_5079_, v_hs_u2081_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
    return v___x_5080_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(
    mut v_useAfter_5081_: *mut crate::leanh::LeanObject,
    mut v_lctx_u2080_5082_: *mut crate::leanh::LeanObject,
    mut v_hs_u2081_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
    mut v_a_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
    mut v_a_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_5089_: u8 = 0;
    let mut v_res_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5089_ = (crate::leanh::lean_unbox(v_useAfter_5081_) as u8);
    v_res_5090_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(
        v_useAfter_boxed_5089_,
        v_lctx_u2080_5082_,
        v_hs_u2081_5083_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
        v_a_5087_,
    );
    crate::leanh::lean_dec(v_a_5087_);
    crate::leanh::lean_dec_ref(v_a_5086_);
    crate::leanh::lean_dec(v_a_5085_);
    crate::leanh::lean_dec_ref(v_a_5084_);
    crate::leanh::lean_dec_ref(v_lctx_u2080_5082_);
    return v_res_5090_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5095_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1;
    v___x_5096_ = l_Lean_stringToMessageData(v___x_5095_);
    return v___x_5096_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5098_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3;
    v___x_5099_ = l_Lean_stringToMessageData(v___x_5098_);
    return v___x_5099_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5101_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5;
    v___x_5102_ = l_Lean_stringToMessageData(v___x_5101_);
    return v___x_5102_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(
    mut v_useAfter_5103_: u8,
    mut v_g_u2080_5104_: *mut crate::leanh::LeanObject,
    mut v_i_u2081_5105_: *mut crate::leanh::LeanObject,
    mut v_a_5106_: *mut crate::leanh::LeanObject,
    mut v_a_5107_: *mut crate::leanh::LeanObject,
    mut v_a_5108_: *mut crate::leanh::LeanObject,
    mut v_a_5109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v_userName_x3f_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v_hyps_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5137_: u8 = 0;
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_a_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_a_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_unused_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5218_: u8 = 0;
    let mut v_unused_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5111_ = lean_st_ref_get(v_a_5107_);
                v_mctx_5112_ = crate::leanh::lean_ctor_get(v___x_5111_, 0);
                crate::leanh::lean_inc_ref(v_mctx_5112_);
                crate::leanh::lean_dec(v___x_5111_);
                v___x_5113_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5112_, v_g_u2080_5104_);
                crate::leanh::lean_dec_ref(v_mctx_5112_);
                if crate::leanh::lean_obj_tag(v___x_5113_) == 1 {
                    v_val_5114_ = crate::leanh::lean_ctor_get(v___x_5113_, 0);
                    crate::leanh::lean_inc(v_val_5114_);
                    crate::leanh::lean_dec_ref_known(v___x_5113_, 1);
                    v_options_5115_ = crate::leanh::lean_ctor_get(v_a_5108_, 2);
                    v_lctx_5116_ = crate::leanh::lean_ctor_get(v_val_5114_, 1);
                    crate::leanh::lean_inc_ref(v_lctx_5116_);
                    crate::leanh::lean_dec(v_val_5114_);
                    v___x_5117_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc_ref(v_options_5115_);
                    v___x_5118_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5118_, 0, v_options_5115_);
                    crate::leanh::lean_ctor_set(v___x_5118_, 1, v___x_5117_);
                    crate::leanh::lean_ctor_set(v___x_5118_, 2, v___x_5117_);
                    v___x_5119_ = l_Lean_LocalContext_sanitizeNames(v_lctx_5116_, v___x_5118_);
                    v_toInteractiveGoalCore_5120_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 0);
                    crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5120_);
                    v_fst_5121_ = crate::leanh::lean_ctor_get(v___x_5119_, 0);
                    v_isSharedCheck_5218_ = (!crate::leanh::lean_is_exclusive(v___x_5119_)) as u8;
                    if v_isSharedCheck_5218_ == 0 {
                        v_unused_5219_ = crate::leanh::lean_ctor_get(v___x_5119_, 1);
                        crate::leanh::lean_dec(v_unused_5219_);
                        v___x_5123_ = v___x_5119_;
                        v_isShared_5124_ = v_isSharedCheck_5218_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_5121_);
                        crate::leanh::lean_dec(v___x_5119_);
                        v___x_5123_ = crate::leanh::lean_box(0);
                        v_isShared_5124_ = v_isSharedCheck_5218_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5113_);
                    crate::leanh::lean_dec_ref(v_i_u2081_5105_);
                    v___x_5220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
                    v___x_5221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5221_, 0, v_g_u2080_5104_);
                    v___x_5222_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5222_, 0, v___x_5220_);
                    crate::leanh::lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                    v___x_5223_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
                    v___x_5224_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5224_, 0, v___x_5222_);
                    crate::leanh::lean_ctor_set(v___x_5224_, 1, v___x_5223_);
                    v___x_5225_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_5224_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
                    return v___x_5225_;
                }
            }
            1 => {
                v_userName_x3f_5125_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 1);
                v_goalPrefix_5126_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 2);
                v_mvarId_5127_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 3);
                v_isRemoved_x3f_5128_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 5);
                v_isSharedCheck_5215_ = (!crate::leanh::lean_is_exclusive(v_i_u2081_5105_)) as u8;
                if v_isSharedCheck_5215_ == 0 {
                    v_unused_5216_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 4);
                    crate::leanh::lean_dec(v_unused_5216_);
                    v_unused_5217_ = crate::leanh::lean_ctor_get(v_i_u2081_5105_, 0);
                    crate::leanh::lean_dec(v_unused_5217_);
                    v___x_5130_ = v_i_u2081_5105_;
                    v_isShared_5131_ = v_isSharedCheck_5215_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isRemoved_x3f_5128_);
                    crate::leanh::lean_inc(v_mvarId_5127_);
                    crate::leanh::lean_inc(v_goalPrefix_5126_);
                    crate::leanh::lean_inc(v_userName_x3f_5125_);
                    crate::leanh::lean_dec(v_i_u2081_5105_);
                    v___x_5130_ = crate::leanh::lean_box(0);
                    v_isShared_5131_ = v_isSharedCheck_5215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hyps_5132_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5120_, 0);
                v_type_5133_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5120_, 1);
                v_ctx_5134_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5120_, 2);
                v_isSharedCheck_5214_ =
                    (!crate::leanh::lean_is_exclusive(v_toInteractiveGoalCore_5120_)) as u8;
                if v_isSharedCheck_5214_ == 0 {
                    v___x_5136_ = v_toInteractiveGoalCore_5120_;
                    v_isShared_5137_ = v_isSharedCheck_5214_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ctx_5134_);
                    crate::leanh::lean_inc(v_type_5133_);
                    crate::leanh::lean_inc(v_hyps_5132_);
                    crate::leanh::lean_dec(v_toInteractiveGoalCore_5120_);
                    v___x_5136_ = crate::leanh::lean_box(0);
                    v_isShared_5137_ = v_isSharedCheck_5214_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5138_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(
                    v_useAfter_5103_,
                    v_fst_5121_,
                    v_hyps_5132_,
                    v_a_5106_,
                    v_a_5107_,
                    v_a_5108_,
                    v_a_5109_,
                );
                crate::leanh::lean_dec(v_fst_5121_);
                if crate::leanh::lean_obj_tag(v___x_5138_) == 0 {
                    v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                    crate::leanh::lean_inc(v_a_5139_);
                    crate::leanh::lean_dec_ref_known(v___x_5138_, 1);
                    v___x_5140_ = l_Lean_Expr_mvar___override(v_g_u2080_5104_);
                    crate::leanh::lean_inc(v_a_5109_);
                    crate::leanh::lean_inc_ref(v_a_5108_);
                    crate::leanh::lean_inc(v_a_5107_);
                    crate::leanh::lean_inc_ref(v_a_5106_);
                    v___x_5141_ =
                        lean_infer_type(v___x_5140_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
                    if crate::leanh::lean_obj_tag(v___x_5141_) == 0 {
                        v_a_5142_ = crate::leanh::lean_ctor_get(v___x_5141_, 0);
                        crate::leanh::lean_inc(v_a_5142_);
                        crate::leanh::lean_dec_ref_known(v___x_5141_, 1);
                        v___x_5143_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_5142_, v_a_5107_);
                        v_a_5144_ = crate::leanh::lean_ctor_get(v___x_5143_, 0);
                        v_isSharedCheck_5197_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5143_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5146_ = v___x_5143_;
                            v_isShared_5147_ = v_isSharedCheck_5197_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5144_);
                            crate::leanh::lean_dec(v___x_5143_);
                            v___x_5146_ = crate::leanh::lean_box(0);
                            v_isShared_5147_ = v_isSharedCheck_5197_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5139_);
                        crate::leanh::lean_del_object(v___x_5136_);
                        crate::leanh::lean_dec_ref(v_ctx_5134_);
                        crate::leanh::lean_dec_ref(v_type_5133_);
                        crate::leanh::lean_del_object(v___x_5130_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_5128_);
                        crate::leanh::lean_dec(v_mvarId_5127_);
                        crate::leanh::lean_dec_ref(v_goalPrefix_5126_);
                        crate::leanh::lean_dec(v_userName_x3f_5125_);
                        crate::leanh::lean_del_object(v___x_5123_);
                        v_a_5198_ = crate::leanh::lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5205_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5141_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5198_);
                            crate::leanh::lean_dec(v___x_5141_);
                            v___x_5200_ = crate::leanh::lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5136_);
                    crate::leanh::lean_dec_ref(v_ctx_5134_);
                    crate::leanh::lean_dec_ref(v_type_5133_);
                    crate::leanh::lean_del_object(v___x_5130_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_5128_);
                    crate::leanh::lean_dec(v_mvarId_5127_);
                    crate::leanh::lean_dec_ref(v_goalPrefix_5126_);
                    crate::leanh::lean_dec(v_userName_x3f_5125_);
                    crate::leanh::lean_del_object(v___x_5123_);
                    crate::leanh::lean_dec(v_g_u2080_5104_);
                    v_a_5206_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                    v_isSharedCheck_5213_ = (!crate::leanh::lean_is_exclusive(v___x_5138_)) as u8;
                    if v_isSharedCheck_5213_ == 0 {
                        v___x_5208_ = v___x_5138_;
                        v_isShared_5209_ = v_isSharedCheck_5213_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5206_);
                        crate::leanh::lean_dec(v___x_5138_);
                        v___x_5208_ = crate::leanh::lean_box(0);
                        v_isShared_5209_ = v_isSharedCheck_5213_;
                        state = 17;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5148_ = lean_st_ref_get(v_a_5107_);
                v_mctx_5149_ = crate::leanh::lean_ctor_get(v___x_5148_, 0);
                crate::leanh::lean_inc_ref(v_mctx_5149_);
                crate::leanh::lean_dec(v___x_5148_);
                v___x_5150_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5149_, v_mvarId_5127_);
                crate::leanh::lean_dec_ref(v_mctx_5149_);
                if crate::leanh::lean_obj_tag(v___x_5150_) == 1 {
                    crate::leanh::lean_del_object(v___x_5146_);
                    crate::leanh::lean_del_object(v___x_5123_);
                    v_val_5151_ = crate::leanh::lean_ctor_get(v___x_5150_, 0);
                    crate::leanh::lean_inc(v_val_5151_);
                    crate::leanh::lean_dec_ref_known(v___x_5150_, 1);
                    v_type_5152_ = crate::leanh::lean_ctor_get(v_val_5151_, 2);
                    crate::leanh::lean_inc_ref(v_type_5152_);
                    crate::leanh::lean_dec(v_val_5151_);
                    v___x_5153_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_5152_, v_a_5107_);
                    v_a_5154_ = crate::leanh::lean_ctor_get(v___x_5153_, 0);
                    crate::leanh::lean_inc(v_a_5154_);
                    crate::leanh::lean_dec_ref(v___x_5153_);
                    v___x_5155_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
                        v_a_5144_,
                        v_a_5154_,
                        v_useAfter_5103_,
                        v_a_5106_,
                        v_a_5107_,
                        v_a_5108_,
                        v_a_5109_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5155_) == 0 {
                        v_a_5156_ = crate::leanh::lean_ctor_get(v___x_5155_, 0);
                        crate::leanh::lean_inc(v_a_5156_);
                        crate::leanh::lean_dec_ref_known(v___x_5155_, 1);
                        v___x_5157_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
                            v_useAfter_5103_,
                            v_a_5156_,
                            v_type_5133_,
                            v_a_5106_,
                            v_a_5107_,
                            v_a_5108_,
                            v_a_5109_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5157_) == 0 {
                            v_a_5158_ = crate::leanh::lean_ctor_get(v___x_5157_, 0);
                            v_isSharedCheck_5172_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5172_ == 0 {
                                v___x_5160_ = v___x_5157_;
                                v_isShared_5161_ = v_isSharedCheck_5172_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5158_);
                                crate::leanh::lean_dec(v___x_5157_);
                                v___x_5160_ = crate::leanh::lean_box(0);
                                v_isShared_5161_ = v_isSharedCheck_5172_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5139_);
                            crate::leanh::lean_del_object(v___x_5136_);
                            crate::leanh::lean_dec_ref(v_ctx_5134_);
                            crate::leanh::lean_del_object(v___x_5130_);
                            crate::leanh::lean_dec(v_isRemoved_x3f_5128_);
                            crate::leanh::lean_dec(v_mvarId_5127_);
                            crate::leanh::lean_dec_ref(v_goalPrefix_5126_);
                            crate::leanh::lean_dec(v_userName_x3f_5125_);
                            v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5157_, 0);
                            v_isSharedCheck_5180_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5175_ = v___x_5157_;
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5173_);
                                crate::leanh::lean_dec(v___x_5157_);
                                v___x_5175_ = crate::leanh::lean_box(0);
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5139_);
                        crate::leanh::lean_del_object(v___x_5136_);
                        crate::leanh::lean_dec_ref(v_ctx_5134_);
                        crate::leanh::lean_dec_ref(v_type_5133_);
                        crate::leanh::lean_del_object(v___x_5130_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_5128_);
                        crate::leanh::lean_dec(v_mvarId_5127_);
                        crate::leanh::lean_dec_ref(v_goalPrefix_5126_);
                        crate::leanh::lean_dec(v_userName_x3f_5125_);
                        v_a_5181_ = crate::leanh::lean_ctor_get(v___x_5155_, 0);
                        v_isSharedCheck_5188_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5155_)) as u8;
                        if v_isSharedCheck_5188_ == 0 {
                            v___x_5183_ = v___x_5155_;
                            v_isShared_5184_ = v_isSharedCheck_5188_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5181_);
                            crate::leanh::lean_dec(v___x_5155_);
                            v___x_5183_ = crate::leanh::lean_box(0);
                            v_isShared_5184_ = v_isSharedCheck_5188_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5150_);
                    crate::leanh::lean_dec(v_a_5144_);
                    crate::leanh::lean_dec(v_a_5139_);
                    crate::leanh::lean_del_object(v___x_5136_);
                    crate::leanh::lean_dec_ref(v_ctx_5134_);
                    crate::leanh::lean_dec_ref(v_type_5133_);
                    crate::leanh::lean_del_object(v___x_5130_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_5128_);
                    crate::leanh::lean_dec_ref(v_goalPrefix_5126_);
                    crate::leanh::lean_dec(v_userName_x3f_5125_);
                    v___x_5189_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
                    if v_isShared_5147_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5146_, 1);
                        crate::leanh::lean_ctor_set(v___x_5146_, 0, v_mvarId_5127_);
                        v___x_5191_ = v___x_5146_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_mvarId_5127_);
                        v___x_5191_ = v_reuseFailAlloc_5196_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5136_, 1, v_a_5158_);
                    crate::leanh::lean_ctor_set(v___x_5136_, 0, v_a_5139_);
                    v___x_5163_ = v___x_5136_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 1, v_a_5158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 2, v_ctx_5134_);
                    v___x_5163_ = v_reuseFailAlloc_5171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5164_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0;
                if v_isShared_5131_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5130_, 4, v___x_5164_);
                    crate::leanh::lean_ctor_set(v___x_5130_, 0, v___x_5163_);
                    v___x_5166_ = v___x_5130_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_userName_x3f_5125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_goalPrefix_5126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 3, v_mvarId_5127_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 4, v___x_5164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 5, v_isRemoved_x3f_5128_);
                    v___x_5166_ = v_reuseFailAlloc_5170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5160_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
                    v___x_5168_ = v_reuseFailAlloc_5169_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5168_;
            }
            9 => {
                if v_isShared_5176_ == 0 {
                    v___x_5178_ = v___x_5175_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5178_;
            }
            11 => {
                if v_isShared_5184_ == 0 {
                    v___x_5186_ = v___x_5183_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5187_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5186_;
            }
            13 => {
                if v_isShared_5124_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5123_, 7);
                    crate::leanh::lean_ctor_set(v___x_5123_, 1, v___x_5191_);
                    crate::leanh::lean_ctor_set(v___x_5123_, 0, v___x_5189_);
                    v___x_5193_ = v___x_5123_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5195_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5195_, 0, v___x_5189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5195_, 1, v___x_5191_);
                    v___x_5193_ = v_reuseFailAlloc_5195_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5194_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_5193_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
                return v___x_5194_;
            }
            15 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5203_;
            }
            17 => {
                if v_isShared_5209_ == 0 {
                    v___x_5211_ = v___x_5208_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
                    v___x_5211_ = v_reuseFailAlloc_5212_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___boxed(
    mut v_useAfter_5226_: *mut crate::leanh::LeanObject,
    mut v_g_u2080_5227_: *mut crate::leanh::LeanObject,
    mut v_i_u2081_5228_: *mut crate::leanh::LeanObject,
    mut v_a_5229_: *mut crate::leanh::LeanObject,
    mut v_a_5230_: *mut crate::leanh::LeanObject,
    mut v_a_5231_: *mut crate::leanh::LeanObject,
    mut v_a_5232_: *mut crate::leanh::LeanObject,
    mut v_a_5233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_5234_: u8 = 0;
    let mut v_res_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5234_ = (crate::leanh::lean_unbox(v_useAfter_5226_) as u8);
    v_res_5235_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(
        v_useAfter_boxed_5234_,
        v_g_u2080_5227_,
        v_i_u2081_5228_,
        v_a_5229_,
        v_a_5230_,
        v_a_5231_,
        v_a_5232_,
    );
    crate::leanh::lean_dec(v_a_5232_);
    crate::leanh::lean_dec_ref(v_a_5231_);
    crate::leanh::lean_dec(v_a_5230_);
    crate::leanh::lean_dec_ref(v_a_5229_);
    return v_res_5235_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
    mut v_opts_5236_: *mut crate::leanh::LeanObject,
    mut v_opt_5237_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5238_ = crate::leanh::lean_ctor_get(v_opt_5237_, 0);
    v_defValue_5239_ = crate::leanh::lean_ctor_get(v_opt_5237_, 1);
    v_map_5240_ = crate::leanh::lean_ctor_get(v_opts_5236_, 0);
    v___x_5241_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5240_,
            v_name_5238_,
        );
    if crate::leanh::lean_obj_tag(v___x_5241_) == 0 {
        let mut v___x_5242_: u8 = 0;
        v___x_5242_ = (crate::leanh::lean_unbox(v_defValue_5239_) as u8);
        return v___x_5242_;
    } else {
        let mut v_val_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5243_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
        crate::leanh::lean_inc(v_val_5243_);
        crate::leanh::lean_dec_ref_known(v___x_5241_, 1);
        if crate::leanh::lean_obj_tag(v_val_5243_) == 1 {
            let mut v_v_5244_: u8 = 0;
            v_v_5244_ = crate::leanh::lean_ctor_get_uint8(v_val_5243_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5243_, 0);
            return v_v_5244_;
        } else {
            let mut v___x_5245_: u8 = 0;
            crate::leanh::lean_dec(v_val_5243_);
            v___x_5245_ = (crate::leanh::lean_unbox(v_defValue_5239_) as u8);
            return v___x_5245_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(
    mut v_opts_5246_: *mut crate::leanh::LeanObject,
    mut v_opt_5247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5248_: u8 = 0;
    let mut v_r_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
        v_opts_5246_,
        v_opt_5247_,
    );
    crate::leanh::lean_dec_ref(v_opt_5247_);
    crate::leanh::lean_dec_ref(v_opts_5246_);
    v_r_5249_ = crate::leanh::lean_box((v_res_5248_) as usize);
    return v_r_5249_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
    mut v_x_5250_: *mut crate::leanh::LeanObject,
    mut v_x_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5251_) == 0 {
                    v___x_5257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5257_, 0, v_x_5250_);
                    return v___x_5257_;
                } else {
                    v_head_5258_ = crate::leanh::lean_ctor_get(v_x_5251_, 0);
                    crate::leanh::lean_inc_n(v_head_5258_, 2);
                    v_tail_5259_ = crate::leanh::lean_ctor_get(v_x_5251_, 1);
                    crate::leanh::lean_inc(v_tail_5259_);
                    crate::leanh::lean_dec_ref_known(v_x_5251_, 2);
                    v___x_5260_ = l_Lean_Expr_mvar___override(v_head_5258_);
                    v___x_5261_ = l_Lean_Meta_getMVars(
                        v___x_5260_,
                        v___y_5252_,
                        v___y_5253_,
                        v___y_5254_,
                        v___y_5255_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5261_) == 0 {
                        v_a_5262_ = crate::leanh::lean_ctor_get(v___x_5261_, 0);
                        crate::leanh::lean_inc(v_a_5262_);
                        crate::leanh::lean_dec_ref_known(v___x_5261_, 1);
                        v___x_5263_ = l_Lean_MVarIdSet_ofArray(v_a_5262_);
                        crate::leanh::lean_dec(v_a_5262_);
                        v___x_5264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_5258_, v___x_5263_, v_x_5250_);
                        v_x_5250_ = v___x_5264_;
                        v_x_5251_ = v_tail_5259_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5259_);
                        crate::leanh::lean_dec(v_head_5258_);
                        crate::leanh::lean_dec(v_x_5250_);
                        v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5261_, 0);
                        v_isSharedCheck_5273_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5261_)) as u8;
                        if v_isSharedCheck_5273_ == 0 {
                            v___x_5268_ = v___x_5261_;
                            v_isShared_5269_ = v_isSharedCheck_5273_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5266_);
                            crate::leanh::lean_dec(v___x_5261_);
                            v___x_5268_ = crate::leanh::lean_box(0);
                            v_isShared_5269_ = v_isSharedCheck_5273_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5269_ == 0 {
                    v___x_5271_ = v___x_5268_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
                    v___x_5271_ = v_reuseFailAlloc_5272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1___boxed(
    mut v_x_5274_: *mut crate::leanh::LeanObject,
    mut v_x_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5281_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
        v_x_5274_,
        v_x_5275_,
        v___y_5276_,
        v___y_5277_,
        v___y_5278_,
        v___y_5279_,
    );
    crate::leanh::lean_dec(v___y_5279_);
    crate::leanh::lean_dec_ref(v___y_5278_);
    crate::leanh::lean_dec(v___y_5277_);
    crate::leanh::lean_dec_ref(v___y_5276_);
    return v_res_5281_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(
    mut v_lctx_5282_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5283_: *mut crate::leanh::LeanObject,
    mut v_x_5284_: *mut crate::leanh::LeanObject,
    mut v___y_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
    mut v___y_5287_: *mut crate::leanh::LeanObject,
    mut v___y_5288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut v_a_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    crate::leanh::lean_box(0),
                    v_lctx_5282_,
                    v_localInsts_5283_,
                    v_x_5284_,
                    v___y_5285_,
                    v___y_5286_,
                    v___y_5287_,
                    v___y_5288_,
                );
                if crate::leanh::lean_obj_tag(v___x_5290_) == 0 {
                    v_a_5291_ = crate::leanh::lean_ctor_get(v___x_5290_, 0);
                    v_isSharedCheck_5298_ = (!crate::leanh::lean_is_exclusive(v___x_5290_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5290_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5291_);
                        crate::leanh::lean_dec(v___x_5290_);
                        v___x_5293_ = crate::leanh::lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5299_ = crate::leanh::lean_ctor_get(v___x_5290_, 0);
                    v_isSharedCheck_5306_ = (!crate::leanh::lean_is_exclusive(v___x_5290_)) as u8;
                    if v_isSharedCheck_5306_ == 0 {
                        v___x_5301_ = v___x_5290_;
                        v_isShared_5302_ = v_isSharedCheck_5306_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5299_);
                        crate::leanh::lean_dec(v___x_5290_);
                        v___x_5301_ = crate::leanh::lean_box(0);
                        v_isShared_5302_ = v_isSharedCheck_5306_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5294_ == 0 {
                    v___x_5296_ = v___x_5293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
                    v___x_5296_ = v_reuseFailAlloc_5297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5296_;
            }
            3 => {
                if v_isShared_5302_ == 0 {
                    v___x_5304_ = v___x_5301_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
                    v___x_5304_ = v_reuseFailAlloc_5305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg___boxed(
    mut v_lctx_5307_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5308_: *mut crate::leanh::LeanObject,
    mut v_x_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_5307_, v_localInsts_5308_, v_x_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
    crate::leanh::lean_dec(v___y_5313_);
    crate::leanh::lean_dec_ref(v___y_5312_);
    crate::leanh::lean_dec(v___y_5311_);
    crate::leanh::lean_dec_ref(v___y_5310_);
    return v_res_5315_;
}
pub unsafe fn _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0;
    v___x_5318_ = l_Lean_stringToMessageData(v___x_5317_);
    return v___x_5318_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(
    mut v_goal_5319_: *mut crate::leanh::LeanObject,
    mut v_action_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = lean_st_ref_get(v___y_5322_);
    v_mctx_5327_ = crate::leanh::lean_ctor_get(v___x_5326_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5327_);
    crate::leanh::lean_dec(v___x_5326_);
    v___x_5328_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5327_, v_goal_5319_);
    crate::leanh::lean_dec_ref(v_mctx_5327_);
    if crate::leanh::lean_obj_tag(v___x_5328_) == 1 {
        let mut v_val_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_options_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lctx_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_localInstances_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_goal_5319_);
        v_val_5329_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
        crate::leanh::lean_inc(v_val_5329_);
        crate::leanh::lean_dec_ref_known(v___x_5328_, 1);
        v_options_5330_ = crate::leanh::lean_ctor_get(v___y_5323_, 2);
        v_lctx_5331_ = crate::leanh::lean_ctor_get(v_val_5329_, 1);
        v_localInstances_5332_ = crate::leanh::lean_ctor_get(v_val_5329_, 4);
        crate::leanh::lean_inc_ref(v_localInstances_5332_);
        v___x_5333_ = crate::leanh::lean_box(1);
        crate::leanh::lean_inc_ref(v_options_5330_);
        v___x_5334_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5334_, 0, v_options_5330_);
        crate::leanh::lean_ctor_set(v___x_5334_, 1, v___x_5333_);
        crate::leanh::lean_ctor_set(v___x_5334_, 2, v___x_5333_);
        crate::leanh::lean_inc_ref(v_lctx_5331_);
        v___x_5335_ = l_Lean_LocalContext_sanitizeNames(v_lctx_5331_, v___x_5334_);
        v_fst_5336_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
        crate::leanh::lean_inc_n(v_fst_5336_, 2);
        crate::leanh::lean_dec_ref(v___x_5335_);
        v___x_5337_ = crate::leanh::lean_apply_2(v_action_5320_, v_fst_5336_, v_val_5329_);
        v___x_5338_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_5336_, v_localInstances_5332_, v___x_5337_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
        return v___x_5338_;
    } else {
        let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_5328_);
        crate::leanh::lean_dec_ref(v_action_5320_);
        v___x_5339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once), _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
        v___x_5340_ = l_Lean_MessageData_ofName(v_goal_5319_);
        v___x_5341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5339_);
        crate::leanh::lean_ctor_set(v___x_5341_, 1, v___x_5340_);
        v___x_5342_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_5341_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
        return v___x_5342_;
    }
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(
    mut v_goal_5343_: *mut crate::leanh::LeanObject,
    mut v_action_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5350_ =
        l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(
            v_goal_5343_,
            v_action_5344_,
            v___y_5345_,
            v___y_5346_,
            v___y_5347_,
            v___y_5348_,
        );
    crate::leanh::lean_dec(v___y_5348_);
    crate::leanh::lean_dec_ref(v___y_5347_);
    crate::leanh::lean_dec(v___y_5346_);
    crate::leanh::lean_dec_ref(v___y_5345_);
    return v_res_5350_;
}
pub unsafe fn l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(
    mut v___x_5351_: *mut crate::leanh::LeanObject,
    mut v_x_5352_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5353_: u8 = 0;
    let mut v_head_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5352_) == 0 {
                    v___x_5353_ = 0;
                    return v___x_5353_;
                } else {
                    v_head_5354_ = crate::leanh::lean_ctor_get(v_x_5352_, 0);
                    v_tail_5355_ = crate::leanh::lean_ctor_get(v_x_5352_, 1);
                    v___x_5356_ = l_Lean_instBEqMVarId_beq(v_head_5354_, v___x_5351_);
                    if v___x_5356_ == 0 {
                        v_x_5352_ = v_tail_5355_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5356_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4___boxed(
    mut v___x_5358_: *mut crate::leanh::LeanObject,
    mut v_x_5359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5360_: u8 = 0;
    let mut v_r_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5360_ =
        l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_5358_, v_x_5359_);
    crate::leanh::lean_dec(v_x_5359_);
    crate::leanh::lean_dec(v___x_5358_);
    v_r_5361_ = crate::leanh::lean_box((v_res_5360_) as usize);
    return v_r_5361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(
    mut v_t_5362_: *mut crate::leanh::LeanObject,
    mut v_k_5363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: u8 = 0;
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_5362_) == 0 {
                    v_k_5364_ = crate::leanh::lean_ctor_get(v_t_5362_, 1);
                    v_v_5365_ = crate::leanh::lean_ctor_get(v_t_5362_, 2);
                    v_l_5366_ = crate::leanh::lean_ctor_get(v_t_5362_, 3);
                    v_r_5367_ = crate::leanh::lean_ctor_get(v_t_5362_, 4);
                    v___x_5368_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5363_, v_k_5364_);
                    match v___x_5368_ {
                        0 => {
                            v_t_5362_ = v_l_5366_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_5365_);
                            v___x_5370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5370_, 0, v_v_5365_);
                            return v___x_5370_;
                        }
                        _ => {
                            v_t_5362_ = v_r_5367_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5372_ = crate::leanh::lean_box(0);
                    return v___x_5372_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(
    mut v_t_5373_: *mut crate::leanh::LeanObject,
    mut v_k_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_5373_, v_k_5374_);
    crate::leanh::lean_dec(v_k_5374_);
    crate::leanh::lean_dec(v_t_5373_);
    return v_res_5375_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(
    mut v_k_5376_: *mut crate::leanh::LeanObject,
    mut v_t_5377_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_5377_) == 0 {
                    v_k_5378_ = crate::leanh::lean_ctor_get(v_t_5377_, 1);
                    v_l_5379_ = crate::leanh::lean_ctor_get(v_t_5377_, 3);
                    v_r_5380_ = crate::leanh::lean_ctor_get(v_t_5377_, 4);
                    v___x_5381_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5376_, v_k_5378_);
                    match v___x_5381_ {
                        0 => {
                            v_t_5377_ = v_l_5379_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_5383_ = 1;
                            return v___x_5383_;
                        }
                        _ => {
                            v_t_5377_ = v_r_5380_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5385_ = 0;
                    return v___x_5385_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg___boxed(
    mut v_k_5386_: *mut crate::leanh::LeanObject,
    mut v_t_5387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5388_: u8 = 0;
    let mut v_r_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_5386_, v_t_5387_);
    crate::leanh::lean_dec(v_t_5387_);
    crate::leanh::lean_dec(v_k_5386_);
    v_r_5389_ = crate::leanh::lean_box((v_res_5388_) as usize);
    return v_r_5389_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(
    mut v_a_5390_: *mut crate::leanh::LeanObject,
    mut v___x_5391_: u8,
    mut v_before_5392_: *mut crate::leanh::LeanObject,
    mut v_after_5393_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_5390_, v_before_5392_);
    if crate::leanh::lean_obj_tag(v___x_5394_) == 0 {
        return v___x_5391_;
    } else {
        let mut v_val_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5396_: u8 = 0;
        v_val_5395_ = crate::leanh::lean_ctor_get(v___x_5394_, 0);
        crate::leanh::lean_inc(v_val_5395_);
        crate::leanh::lean_dec_ref_known(v___x_5394_, 1);
        v___x_5396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_5393_, v_val_5395_);
        crate::leanh::lean_dec(v_val_5395_);
        return v___x_5396_;
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(
    mut v_a_5397_: *mut crate::leanh::LeanObject,
    mut v___x_5398_: *mut crate::leanh::LeanObject,
    mut v_before_5399_: *mut crate::leanh::LeanObject,
    mut v_after_5400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3864__boxed_5401_: u8 = 0;
    let mut v_res_5402_: u8 = 0;
    let mut v_r_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3864__boxed_5401_ = (crate::leanh::lean_unbox(v___x_5398_) as u8);
    v_res_5402_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(
        v_a_5397_,
        v___x_3864__boxed_5401_,
        v_before_5399_,
        v_after_5400_,
    );
    crate::leanh::lean_dec(v_after_5400_);
    crate::leanh::lean_dec(v_before_5399_);
    crate::leanh::lean_dec(v_a_5397_);
    v_r_5403_ = crate::leanh::lean_box((v_res_5402_) as usize);
    return v_r_5403_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
    mut v___y_5404_: u8,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
    mut v___x_5406_: *mut crate::leanh::LeanObject,
    mut v_x_5407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: u8 = 0;
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5407_) == 0 {
                    v___x_5408_ = crate::leanh::lean_box(0);
                    return v___x_5408_;
                } else {
                    v_head_5409_ = crate::leanh::lean_ctor_get(v_x_5407_, 0);
                    v_tail_5410_ = crate::leanh::lean_ctor_get(v_x_5407_, 1);
                    v___x_5415_ = 0;
                    if v___y_5404_ == 0 {
                        v___x_5416_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_5405_, v___x_5415_, v___x_5406_, v_head_5409_);
                        v___y_5412_ = v___x_5416_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5417_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(v_a_5405_, v___x_5415_, v_head_5409_, v___x_5406_);
                        v___y_5412_ = v___x_5417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_5412_ == 0 {
                    v_x_5407_ = v_tail_5410_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_head_5409_);
                    v___x_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5414_, 0, v_head_5409_);
                    return v___x_5414_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v___x_5420_: *mut crate::leanh::LeanObject,
    mut v_x_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3875__boxed_5422_: u8 = 0;
    let mut v_res_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3875__boxed_5422_ = (crate::leanh::lean_unbox(v___y_5418_) as u8);
    v_res_5423_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
        v___y_3875__boxed_5422_,
        v_a_5419_,
        v___x_5420_,
        v_x_5421_,
    );
    crate::leanh::lean_dec(v_x_5421_);
    crate::leanh::lean_dec(v___x_5420_);
    crate::leanh::lean_dec(v_a_5419_);
    return v_res_5423_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(
    mut v_mvarId_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: u8,
    mut v_a_5427_: *mut crate::leanh::LeanObject,
    mut v_useAfter_5428_: u8,
    mut v_v_5429_: *mut crate::leanh::LeanObject,
    mut v___x_5430_: u8,
    mut v_toInteractiveGoalCore_5431_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_5432_: *mut crate::leanh::LeanObject,
    mut v_goalPrefix_5433_: *mut crate::leanh::LeanObject,
    mut v_isInserted_x3f_5434_: *mut crate::leanh::LeanObject,
    mut v_isRemoved_x3f_5435_: *mut crate::leanh::LeanObject,
    mut v___lctx_u2081_5436_: *mut crate::leanh::LeanObject,
    mut v___md_u2081_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5443_: u8 = 0;
    v___x_5443_ =
        l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_5424_, v___y_5425_);
    if v___x_5443_ == 0 {
        let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5444_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
            v___y_5426_,
            v_a_5427_,
            v_mvarId_5424_,
            v___y_5425_,
        );
        if crate::leanh::lean_obj_tag(v___x_5444_) == 1 {
            let mut v_val_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_isRemoved_x3f_5435_);
            crate::leanh::lean_dec(v_isInserted_x3f_5434_);
            crate::leanh::lean_dec_ref(v_goalPrefix_5433_);
            crate::leanh::lean_dec(v_userName_x3f_5432_);
            crate::leanh::lean_dec_ref(v_toInteractiveGoalCore_5431_);
            crate::leanh::lean_dec(v_mvarId_5424_);
            v_val_5445_ = crate::leanh::lean_ctor_get(v___x_5444_, 0);
            crate::leanh::lean_inc(v_val_5445_);
            crate::leanh::lean_dec_ref_known(v___x_5444_, 1);
            v___x_5446_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(
                v_useAfter_5428_,
                v_val_5445_,
                v_v_5429_,
                v___y_5438_,
                v___y_5439_,
                v___y_5440_,
                v___y_5441_,
            );
            return v___x_5446_;
        } else {
            crate::leanh::lean_dec(v___x_5444_);
            crate::leanh::lean_dec(v_v_5429_);
            if v___y_5426_ == 0 {
                let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_isRemoved_x3f_5435_);
                v___x_5447_ = crate::leanh::lean_box((v___x_5430_) as usize);
                v___x_5448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5448_, 0, v___x_5447_);
                v___x_5449_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5449_, 0, v_toInteractiveGoalCore_5431_);
                crate::leanh::lean_ctor_set(v___x_5449_, 1, v_userName_x3f_5432_);
                crate::leanh::lean_ctor_set(v___x_5449_, 2, v_goalPrefix_5433_);
                crate::leanh::lean_ctor_set(v___x_5449_, 3, v_mvarId_5424_);
                crate::leanh::lean_ctor_set(v___x_5449_, 4, v_isInserted_x3f_5434_);
                crate::leanh::lean_ctor_set(v___x_5449_, 5, v___x_5448_);
                v___x_5450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5450_, 0, v___x_5449_);
                return v___x_5450_;
            } else {
                let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_isInserted_x3f_5434_);
                v___x_5451_ = crate::leanh::lean_box((v___x_5430_) as usize);
                v___x_5452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5452_, 0, v___x_5451_);
                v___x_5453_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5453_, 0, v_toInteractiveGoalCore_5431_);
                crate::leanh::lean_ctor_set(v___x_5453_, 1, v_userName_x3f_5432_);
                crate::leanh::lean_ctor_set(v___x_5453_, 2, v_goalPrefix_5433_);
                crate::leanh::lean_ctor_set(v___x_5453_, 3, v_mvarId_5424_);
                crate::leanh::lean_ctor_set(v___x_5453_, 4, v___x_5452_);
                crate::leanh::lean_ctor_set(v___x_5453_, 5, v_isRemoved_x3f_5435_);
                v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                return v___x_5454_;
            }
        }
    } else {
        let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_isInserted_x3f_5434_);
        crate::leanh::lean_dec(v_v_5429_);
        v___x_5455_ = crate::leanh::lean_box(0);
        v___x_5456_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5456_, 0, v_toInteractiveGoalCore_5431_);
        crate::leanh::lean_ctor_set(v___x_5456_, 1, v_userName_x3f_5432_);
        crate::leanh::lean_ctor_set(v___x_5456_, 2, v_goalPrefix_5433_);
        crate::leanh::lean_ctor_set(v___x_5456_, 3, v_mvarId_5424_);
        crate::leanh::lean_ctor_set(v___x_5456_, 4, v___x_5455_);
        crate::leanh::lean_ctor_set(v___x_5456_, 5, v_isRemoved_x3f_5435_);
        v___x_5457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5457_, 0, v___x_5456_);
        return v___x_5457_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_5458_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___y_5459_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___y_5460_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_5461_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_useAfter_5462_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_v_5463_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5464_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_toInteractiveGoalCore_5465_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_userName_x3f_5466_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_goalPrefix_5467_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_isInserted_x3f_5468_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_isRemoved_x3f_5469_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___lctx_u2081_5470_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___md_u2081_5471_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5472_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5473_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5474_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5475_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5476_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3908__boxed_5477_: u8 = 0;
    let mut v_useAfter_boxed_5478_: u8 = 0;
    let mut v___x_3910__boxed_5479_: u8 = 0;
    let mut v_res_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3908__boxed_5477_ = (crate::leanh::lean_unbox(v___y_5460_) as u8);
    v_useAfter_boxed_5478_ = (crate::leanh::lean_unbox(v_useAfter_5462_) as u8);
    v___x_3910__boxed_5479_ = (crate::leanh::lean_unbox(v___x_5464_) as u8);
    v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_5458_, v___y_5459_, v___y_3908__boxed_5477_, v_a_5461_, v_useAfter_boxed_5478_, v_v_5463_, v___x_3910__boxed_5479_, v_toInteractiveGoalCore_5465_, v_userName_x3f_5466_, v_goalPrefix_5467_, v_isInserted_x3f_5468_, v_isRemoved_x3f_5469_, v___lctx_u2081_5470_, v___md_u2081_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
    crate::leanh::lean_dec(v___y_5475_);
    crate::leanh::lean_dec_ref(v___y_5474_);
    crate::leanh::lean_dec(v___y_5473_);
    crate::leanh::lean_dec_ref(v___y_5472_);
    crate::leanh::lean_dec_ref(v___md_u2081_5471_);
    crate::leanh::lean_dec_ref(v___lctx_u2081_5470_);
    crate::leanh::lean_dec(v_a_5461_);
    crate::leanh::lean_dec(v___y_5459_);
    return v_res_5480_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: u8,
    mut v_a_5483_: *mut crate::leanh::LeanObject,
    mut v_useAfter_5484_: u8,
    mut v___x_5485_: u8,
    mut v_sz_5486_: usize,
    mut v_i_5487_: usize,
    mut v_bs_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5494_: u8 = 0;
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: usize = 0;
    let mut v___x_5512_: usize = 0;
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5494_ = lean_usize_dec_lt(v_i_5487_, v_sz_5486_);
                if v___x_5494_ == 0 {
                    crate::leanh::lean_dec(v_a_5483_);
                    crate::leanh::lean_dec(v___y_5481_);
                    v___x_5495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5495_, 0, v_bs_5488_);
                    return v___x_5495_;
                } else {
                    v_v_5496_ = lean_array_uget_borrowed(v_bs_5488_, v_i_5487_);
                    v_toInteractiveGoalCore_5497_ = crate::leanh::lean_ctor_get(v_v_5496_, 0);
                    v_userName_x3f_5498_ = crate::leanh::lean_ctor_get(v_v_5496_, 1);
                    v_goalPrefix_5499_ = crate::leanh::lean_ctor_get(v_v_5496_, 2);
                    v_mvarId_5500_ = crate::leanh::lean_ctor_get(v_v_5496_, 3);
                    v_isInserted_x3f_5501_ = crate::leanh::lean_ctor_get(v_v_5496_, 4);
                    v_isRemoved_x3f_5502_ = crate::leanh::lean_ctor_get(v_v_5496_, 5);
                    v___x_5503_ = crate::leanh::lean_box((v___y_5482_) as usize);
                    v___x_5504_ = crate::leanh::lean_box((v_useAfter_5484_) as usize);
                    v___x_5505_ = crate::leanh::lean_box((v___x_5485_) as usize);
                    crate::leanh::lean_inc(v_isRemoved_x3f_5502_);
                    crate::leanh::lean_inc(v_isInserted_x3f_5501_);
                    crate::leanh::lean_inc_ref(v_goalPrefix_5499_);
                    crate::leanh::lean_inc(v_userName_x3f_5498_);
                    crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5497_);
                    crate::leanh::lean_inc(v_v_5496_);
                    crate::leanh::lean_inc(v_a_5483_);
                    crate::leanh::lean_inc(v___y_5481_);
                    crate::leanh::lean_inc_n(v_mvarId_5500_, 2);
                    v___f_5506_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed as *mut core::ffi::c_void, 19, 12);
                    crate::leanh::lean_closure_set(v___f_5506_, 0, v_mvarId_5500_);
                    crate::leanh::lean_closure_set(v___f_5506_, 1, v___y_5481_);
                    crate::leanh::lean_closure_set(v___f_5506_, 2, v___x_5503_);
                    crate::leanh::lean_closure_set(v___f_5506_, 3, v_a_5483_);
                    crate::leanh::lean_closure_set(v___f_5506_, 4, v___x_5504_);
                    crate::leanh::lean_closure_set(v___f_5506_, 5, v_v_5496_);
                    crate::leanh::lean_closure_set(v___f_5506_, 6, v___x_5505_);
                    crate::leanh::lean_closure_set(v___f_5506_, 7, v_toInteractiveGoalCore_5497_);
                    crate::leanh::lean_closure_set(v___f_5506_, 8, v_userName_x3f_5498_);
                    crate::leanh::lean_closure_set(v___f_5506_, 9, v_goalPrefix_5499_);
                    crate::leanh::lean_closure_set(v___f_5506_, 10, v_isInserted_x3f_5501_);
                    crate::leanh::lean_closure_set(v___f_5506_, 11, v_isRemoved_x3f_5502_);
                    v___x_5507_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_5500_, v___f_5506_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
                    if crate::leanh::lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        crate::leanh::lean_inc(v_a_5508_);
                        crate::leanh::lean_dec_ref_known(v___x_5507_, 1);
                        v___x_5509_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5510_ = lean_array_uset(v_bs_5488_, v_i_5487_, v___x_5509_);
                        v___x_5511_ = 1usize;
                        v___x_5512_ = lean_usize_add(v_i_5487_, v___x_5511_);
                        v___x_5513_ = lean_array_uset(v_bs_x27_5510_, v_i_5487_, v_a_5508_);
                        v_i_5487_ = v___x_5512_;
                        v_bs_5488_ = v___x_5513_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5488_);
                        crate::leanh::lean_dec(v_a_5483_);
                        crate::leanh::lean_dec(v___y_5481_);
                        v_a_5515_ = crate::leanh::lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5522_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5522_ == 0 {
                            v___x_5517_ = v___x_5507_;
                            v_isShared_5518_ = v_isSharedCheck_5522_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5515_);
                            crate::leanh::lean_dec(v___x_5507_);
                            v___x_5517_ = crate::leanh::lean_box(0);
                            v_isShared_5518_ = v_isSharedCheck_5522_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5518_ == 0 {
                    v___x_5520_ = v___x_5517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
                    v___x_5520_ = v_reuseFailAlloc_5521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8___boxed(
    mut v___y_5523_: *mut crate::leanh::LeanObject,
    mut v___y_5524_: *mut crate::leanh::LeanObject,
    mut v_a_5525_: *mut crate::leanh::LeanObject,
    mut v_useAfter_5526_: *mut crate::leanh::LeanObject,
    mut v___x_5527_: *mut crate::leanh::LeanObject,
    mut v_sz_5528_: *mut crate::leanh::LeanObject,
    mut v_i_5529_: *mut crate::leanh::LeanObject,
    mut v_bs_5530_: *mut crate::leanh::LeanObject,
    mut v___y_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3965__boxed_5536_: u8 = 0;
    let mut v_useAfter_boxed_5537_: u8 = 0;
    let mut v___x_3967__boxed_5538_: u8 = 0;
    let mut v_sz_boxed_5539_: usize = 0;
    let mut v_i_boxed_5540_: usize = 0;
    let mut v_res_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3965__boxed_5536_ = (crate::leanh::lean_unbox(v___y_5524_) as u8);
    v_useAfter_boxed_5537_ = (crate::leanh::lean_unbox(v_useAfter_5526_) as u8);
    v___x_3967__boxed_5538_ = (crate::leanh::lean_unbox(v___x_5527_) as u8);
    v_sz_boxed_5539_ = crate::leanh::lean_unbox_usize(v_sz_5528_);
    crate::leanh::lean_dec(v_sz_5528_);
    v_i_boxed_5540_ = crate::leanh::lean_unbox_usize(v_i_5529_);
    crate::leanh::lean_dec(v_i_5529_);
    v_res_5541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_5523_, v___y_3965__boxed_5536_, v_a_5525_, v_useAfter_boxed_5537_, v___x_3967__boxed_5538_, v_sz_boxed_5539_, v_i_boxed_5540_, v_bs_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
    crate::leanh::lean_dec(v___y_5534_);
    crate::leanh::lean_dec_ref(v___y_5533_);
    crate::leanh::lean_dec(v___y_5532_);
    crate::leanh::lean_dec_ref(v___y_5531_);
    return v_res_5541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(
    mut v___y_5542_: u8,
    mut v_a_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v_useAfter_5545_: u8,
    mut v___x_5546_: u8,
    mut v_sz_5547_: usize,
    mut v_i_5548_: usize,
    mut v_bs_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: usize = 0;
    let mut v___x_5573_: usize = 0;
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5555_ = lean_usize_dec_lt(v_i_5548_, v_sz_5547_);
                if v___x_5555_ == 0 {
                    crate::leanh::lean_dec(v___y_5544_);
                    crate::leanh::lean_dec(v_a_5543_);
                    v___x_5556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5556_, 0, v_bs_5549_);
                    return v___x_5556_;
                } else {
                    v_v_5557_ = lean_array_uget_borrowed(v_bs_5549_, v_i_5548_);
                    v_toInteractiveGoalCore_5558_ = crate::leanh::lean_ctor_get(v_v_5557_, 0);
                    v_userName_x3f_5559_ = crate::leanh::lean_ctor_get(v_v_5557_, 1);
                    v_goalPrefix_5560_ = crate::leanh::lean_ctor_get(v_v_5557_, 2);
                    v_mvarId_5561_ = crate::leanh::lean_ctor_get(v_v_5557_, 3);
                    v_isInserted_x3f_5562_ = crate::leanh::lean_ctor_get(v_v_5557_, 4);
                    v_isRemoved_x3f_5563_ = crate::leanh::lean_ctor_get(v_v_5557_, 5);
                    v___x_5564_ = crate::leanh::lean_box((v___y_5542_) as usize);
                    v___x_5565_ = crate::leanh::lean_box((v_useAfter_5545_) as usize);
                    v___x_5566_ = crate::leanh::lean_box((v___x_5546_) as usize);
                    crate::leanh::lean_inc(v_isRemoved_x3f_5563_);
                    crate::leanh::lean_inc(v_isInserted_x3f_5562_);
                    crate::leanh::lean_inc_ref(v_goalPrefix_5560_);
                    crate::leanh::lean_inc(v_userName_x3f_5559_);
                    crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5558_);
                    crate::leanh::lean_inc(v_v_5557_);
                    crate::leanh::lean_inc(v_a_5543_);
                    crate::leanh::lean_inc(v___y_5544_);
                    crate::leanh::lean_inc_n(v_mvarId_5561_, 2);
                    v___f_5567_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed as *mut core::ffi::c_void, 19, 12);
                    crate::leanh::lean_closure_set(v___f_5567_, 0, v_mvarId_5561_);
                    crate::leanh::lean_closure_set(v___f_5567_, 1, v___y_5544_);
                    crate::leanh::lean_closure_set(v___f_5567_, 2, v___x_5564_);
                    crate::leanh::lean_closure_set(v___f_5567_, 3, v_a_5543_);
                    crate::leanh::lean_closure_set(v___f_5567_, 4, v___x_5565_);
                    crate::leanh::lean_closure_set(v___f_5567_, 5, v_v_5557_);
                    crate::leanh::lean_closure_set(v___f_5567_, 6, v___x_5566_);
                    crate::leanh::lean_closure_set(v___f_5567_, 7, v_toInteractiveGoalCore_5558_);
                    crate::leanh::lean_closure_set(v___f_5567_, 8, v_userName_x3f_5559_);
                    crate::leanh::lean_closure_set(v___f_5567_, 9, v_goalPrefix_5560_);
                    crate::leanh::lean_closure_set(v___f_5567_, 10, v_isInserted_x3f_5562_);
                    crate::leanh::lean_closure_set(v___f_5567_, 11, v_isRemoved_x3f_5563_);
                    v___x_5568_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_5561_, v___f_5567_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
                    if crate::leanh::lean_obj_tag(v___x_5568_) == 0 {
                        v_a_5569_ = crate::leanh::lean_ctor_get(v___x_5568_, 0);
                        crate::leanh::lean_inc(v_a_5569_);
                        crate::leanh::lean_dec_ref_known(v___x_5568_, 1);
                        v___x_5570_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5571_ = lean_array_uset(v_bs_5549_, v_i_5548_, v___x_5570_);
                        v___x_5572_ = 1usize;
                        v___x_5573_ = lean_usize_add(v_i_5548_, v___x_5572_);
                        v___x_5574_ = lean_array_uset(v_bs_x27_5571_, v_i_5548_, v_a_5569_);
                        v___x_5575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_5544_, v___y_5542_, v_a_5543_, v_useAfter_5545_, v___x_5546_, v_sz_5547_, v___x_5573_, v___x_5574_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
                        return v___x_5575_;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5549_);
                        crate::leanh::lean_dec(v___y_5544_);
                        crate::leanh::lean_dec(v_a_5543_);
                        v_a_5576_ = crate::leanh::lean_ctor_get(v___x_5568_, 0);
                        v_isSharedCheck_5583_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5568_)) as u8;
                        if v_isSharedCheck_5583_ == 0 {
                            v___x_5578_ = v___x_5568_;
                            v_isShared_5579_ = v_isSharedCheck_5583_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5576_);
                            crate::leanh::lean_dec(v___x_5568_);
                            v___x_5578_ = crate::leanh::lean_box(0);
                            v_isShared_5579_ = v_isSharedCheck_5583_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5579_ == 0 {
                    v___x_5581_ = v___x_5578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
                    v___x_5581_ = v_reuseFailAlloc_5582_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___boxed(
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v_a_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v_useAfter_5587_: *mut crate::leanh::LeanObject,
    mut v___x_5588_: *mut crate::leanh::LeanObject,
    mut v_sz_5589_: *mut crate::leanh::LeanObject,
    mut v_i_5590_: *mut crate::leanh::LeanObject,
    mut v_bs_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4033__boxed_5597_: u8 = 0;
    let mut v_useAfter_boxed_5598_: u8 = 0;
    let mut v___x_4036__boxed_5599_: u8 = 0;
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_4033__boxed_5597_ = (crate::leanh::lean_unbox(v___y_5584_) as u8);
    v_useAfter_boxed_5598_ = (crate::leanh::lean_unbox(v_useAfter_5587_) as u8);
    v___x_4036__boxed_5599_ = (crate::leanh::lean_unbox(v___x_5588_) as u8);
    v_sz_boxed_5600_ = crate::leanh::lean_unbox_usize(v_sz_5589_);
    crate::leanh::lean_dec(v_sz_5589_);
    v_i_boxed_5601_ = crate::leanh::lean_unbox_usize(v_i_5590_);
    crate::leanh::lean_dec(v_i_5590_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v___y_4033__boxed_5597_, v_a_5585_, v___y_5586_, v_useAfter_boxed_5598_, v___x_4036__boxed_5599_, v_sz_boxed_5600_, v_i_boxed_5601_, v_bs_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    crate::leanh::lean_dec(v___y_5595_);
    crate::leanh::lean_dec_ref(v___y_5594_);
    crate::leanh::lean_dec(v___y_5593_);
    crate::leanh::lean_dec_ref(v___y_5592_);
    return v_res_5602_;
}
pub unsafe fn l_Lean_Widget_diffInteractiveGoals(
    mut v_useAfter_5603_: u8,
    mut v_info_5604_: *mut crate::leanh::LeanObject,
    mut v_igs_u2081_5605_: *mut crate::leanh::LeanObject,
    mut v_a_5606_: *mut crate::leanh::LeanObject,
    mut v_a_5607_: *mut crate::leanh::LeanObject,
    mut v_a_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: u8 = 0;
    let mut v___y_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5620_: usize = 0;
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_a_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5611_ = crate::leanh::lean_ctor_get(v_a_5608_, 2);
                v___x_5612_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
                v___x_5613_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
                    v_options_5611_,
                    v___x_5612_,
                );
                if v___x_5613_ == 0 {
                    crate::leanh::lean_dec_ref(v_info_5604_);
                    v___x_5647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5647_, 0, v_igs_u2081_5605_);
                    return v___x_5647_;
                } else {
                    if v_useAfter_5603_ == 0 {
                        v_goalsAfter_5648_ = crate::leanh::lean_ctor_get(v_info_5604_, 4);
                        crate::leanh::lean_inc(v_goalsAfter_5648_);
                        v___y_5615_ = v_goalsAfter_5648_;
                        state = 1;
                        continue;
                    } else {
                        v_goalsBefore_5649_ = crate::leanh::lean_ctor_get(v_info_5604_, 2);
                        crate::leanh::lean_inc(v_goalsBefore_5649_);
                        v___y_5615_ = v_goalsBefore_5649_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_goalsBefore_5616_ = crate::leanh::lean_ctor_get(v_info_5604_, 2);
                crate::leanh::lean_inc(v_goalsBefore_5616_);
                crate::leanh::lean_dec_ref(v_info_5604_);
                v___x_5617_ = crate::leanh::lean_box(1);
                v___x_5618_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
                    v___x_5617_,
                    v_goalsBefore_5616_,
                    v_a_5606_,
                    v_a_5607_,
                    v_a_5608_,
                    v_a_5609_,
                );
                if crate::leanh::lean_obj_tag(v___x_5618_) == 0 {
                    v_a_5619_ = crate::leanh::lean_ctor_get(v___x_5618_, 0);
                    crate::leanh::lean_inc(v_a_5619_);
                    crate::leanh::lean_dec_ref_known(v___x_5618_, 1);
                    v_sz_5620_ = lean_array_size(v_igs_u2081_5605_);
                    v___x_5621_ = 0usize;
                    v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_5603_, v_a_5619_, v___y_5615_, v_useAfter_5603_, v___x_5613_, v_sz_5620_, v___x_5621_, v_igs_u2081_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
                    if crate::leanh::lean_obj_tag(v___x_5622_) == 0 {
                        v_a_5623_ = crate::leanh::lean_ctor_get(v___x_5622_, 0);
                        v_isSharedCheck_5630_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5622_)) as u8;
                        if v_isSharedCheck_5630_ == 0 {
                            v___x_5625_ = v___x_5622_;
                            v_isShared_5626_ = v_isSharedCheck_5630_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5623_);
                            crate::leanh::lean_dec(v___x_5622_);
                            v___x_5625_ = crate::leanh::lean_box(0);
                            v_isShared_5626_ = v_isSharedCheck_5630_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5631_ = crate::leanh::lean_ctor_get(v___x_5622_, 0);
                        v_isSharedCheck_5638_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5622_)) as u8;
                        if v_isSharedCheck_5638_ == 0 {
                            v___x_5633_ = v___x_5622_;
                            v_isShared_5634_ = v_isSharedCheck_5638_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5631_);
                            crate::leanh::lean_dec(v___x_5622_);
                            v___x_5633_ = crate::leanh::lean_box(0);
                            v_isShared_5634_ = v_isSharedCheck_5638_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5615_);
                    crate::leanh::lean_dec_ref(v_igs_u2081_5605_);
                    v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5618_, 0);
                    v_isSharedCheck_5646_ = (!crate::leanh::lean_is_exclusive(v___x_5618_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5618_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5639_);
                        crate::leanh::lean_dec(v___x_5618_);
                        v___x_5641_ = crate::leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5626_ == 0 {
                    v___x_5628_ = v___x_5625_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
                    v___x_5628_ = v_reuseFailAlloc_5629_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5628_;
            }
            4 => {
                if v_isShared_5634_ == 0 {
                    v___x_5636_ = v___x_5633_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
                    v___x_5636_ = v_reuseFailAlloc_5637_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5636_;
            }
            6 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_diffInteractiveGoals___boxed(
    mut v_useAfter_5650_: *mut crate::leanh::LeanObject,
    mut v_info_5651_: *mut crate::leanh::LeanObject,
    mut v_igs_u2081_5652_: *mut crate::leanh::LeanObject,
    mut v_a_5653_: *mut crate::leanh::LeanObject,
    mut v_a_5654_: *mut crate::leanh::LeanObject,
    mut v_a_5655_: *mut crate::leanh::LeanObject,
    mut v_a_5656_: *mut crate::leanh::LeanObject,
    mut v_a_5657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useAfter_boxed_5658_: u8 = 0;
    let mut v_res_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5658_ = (crate::leanh::lean_unbox(v_useAfter_5650_) as u8);
    v_res_5659_ = l_Lean_Widget_diffInteractiveGoals(
        v_useAfter_boxed_5658_,
        v_info_5651_,
        v_igs_u2081_5652_,
        v_a_5653_,
        v_a_5654_,
        v_a_5655_,
        v_a_5656_,
    );
    crate::leanh::lean_dec(v_a_5656_);
    crate::leanh::lean_dec_ref(v_a_5655_);
    crate::leanh::lean_dec(v_a_5654_);
    crate::leanh::lean_dec_ref(v_a_5653_);
    return v_res_5659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(
    mut v_00_u03b4_5660_: *mut crate::leanh::LeanObject,
    mut v_t_5661_: *mut crate::leanh::LeanObject,
    mut v_k_5662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5663_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_5661_, v_k_5662_);
    return v___x_5663_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(
    mut v_00_u03b4_5664_: *mut crate::leanh::LeanObject,
    mut v_t_5665_: *mut crate::leanh::LeanObject,
    mut v_k_5666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_5664_, v_t_5665_, v_k_5666_);
    crate::leanh::lean_dec(v_k_5666_);
    crate::leanh::lean_dec(v_t_5665_);
    return v_res_5667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(
    mut v_00_u03b2_5668_: *mut crate::leanh::LeanObject,
    mut v_k_5669_: *mut crate::leanh::LeanObject,
    mut v_t_5670_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5671_: u8 = 0;
    v___x_5671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_5669_, v_t_5670_);
    return v___x_5671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(
    mut v_00_u03b2_5672_: *mut crate::leanh::LeanObject,
    mut v_k_5673_: *mut crate::leanh::LeanObject,
    mut v_t_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5675_: u8 = 0;
    let mut v_r_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(
            v_00_u03b2_5672_,
            v_k_5673_,
            v_t_5674_,
        );
    crate::leanh::lean_dec(v_t_5674_);
    crate::leanh::lean_dec(v_k_5673_);
    v_r_5676_ = crate::leanh::lean_box((v_res_5675_) as usize);
    return v_r_5676_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(
    mut v_00_u03b1_5677_: *mut crate::leanh::LeanObject,
    mut v_lctx_5678_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5679_: *mut crate::leanh::LeanObject,
    mut v_x_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_5678_, v_localInsts_5679_, v_x_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    return v___x_5686_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(
    mut v_00_u03b1_5687_: *mut crate::leanh::LeanObject,
    mut v_lctx_5688_: *mut crate::leanh::LeanObject,
    mut v_localInsts_5689_: *mut crate::leanh::LeanObject,
    mut v_x_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
    mut v___y_5695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5696_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_5687_, v_lctx_5688_, v_localInsts_5689_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
    crate::leanh::lean_dec(v___y_5694_);
    crate::leanh::lean_dec_ref(v___y_5693_);
    crate::leanh::lean_dec(v___y_5692_);
    crate::leanh::lean_dec_ref(v___y_5691_);
    return v_res_5696_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(
    mut v_00_u03b1_5697_: *mut crate::leanh::LeanObject,
    mut v_goal_5698_: *mut crate::leanh::LeanObject,
    mut v_action_5699_: *mut crate::leanh::LeanObject,
    mut v___y_5700_: *mut crate::leanh::LeanObject,
    mut v___y_5701_: *mut crate::leanh::LeanObject,
    mut v___y_5702_: *mut crate::leanh::LeanObject,
    mut v___y_5703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5705_ =
        l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(
            v_goal_5698_,
            v_action_5699_,
            v___y_5700_,
            v___y_5701_,
            v___y_5702_,
            v___y_5703_,
        );
    return v___x_5705_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___boxed(
    mut v_00_u03b1_5706_: *mut crate::leanh::LeanObject,
    mut v_goal_5707_: *mut crate::leanh::LeanObject,
    mut v_action_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
    mut v___y_5711_: *mut crate::leanh::LeanObject,
    mut v___y_5712_: *mut crate::leanh::LeanObject,
    mut v___y_5713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5714_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(
        v_00_u03b1_5706_,
        v_goal_5707_,
        v_action_5708_,
        v___y_5709_,
        v___y_5710_,
        v___y_5711_,
        v___y_5712_,
    );
    crate::leanh::lean_dec(v___y_5712_);
    crate::leanh::lean_dec_ref(v___y_5711_);
    crate::leanh::lean_dec(v___y_5710_);
    crate::leanh::lean_dec_ref(v___y_5709_);
    return v_res_5714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_Diff(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_Diff(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_Diff(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_InteractiveGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Diff(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_Diff(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_Diff(builtin);
}
