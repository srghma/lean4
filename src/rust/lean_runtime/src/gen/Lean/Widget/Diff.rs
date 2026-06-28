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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 104, 111, 119, 84, 97, 99, 116, 105, 99, 68, 105, 102, 102, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,6622324566003052713 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<86> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [87, 104, 101, 110, 32, 116, 114, 117, 101, 44, 32, 105, 110, 116, 101, 114, 97, 99, 116, 105, 118, 101, 32, 103, 111, 97, 108, 115, 32, 102, 111, 114, 32, 116, 97, 99, 116, 105, 99, 115, 32, 119, 105, 108, 108, 32, 98, 101, 32, 100, 101, 99, 111, 114, 97, 116, 101, 100, 32, 119, 105, 116, 104, 32, 100, 105, 102, 102, 105, 110, 103, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 46, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__2_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__4_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__5_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__7_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,4735983161311130606 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [68, 105, 102, 102, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__9_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__10_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,7775793824594353132 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__11_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,6645386215732740461 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__12_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__6_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,10488261404848132824 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__13_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__8_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,9842793936046282308 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__14_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__0_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject,13397182889434623170 as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiffTag___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value
) as *mut LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value
) as *mut LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__6_value) as *mut LeanObject] };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 101, 102, 111, 114, 101, 58, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [10, 97, 102, 116, 101, 114, 58, 32, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value:
    LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
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
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value
) as *mut LeanObject;
pub static mut l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___closed__4_value
)
    as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 101, 109, 112, 116, 121, 32, 102, 118, 97, 114, 32, 108, 105, 115, 116, 33, 0]};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value:
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
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value:
    LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 107, 110, 111, 119, 110, 32, 103, 111, 97, 108, 32, 0]};
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(
    mut v_name_2858_: *mut LeanObject,
    mut v_decl_2859_: *mut LeanObject,
    mut v_ref_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2862_ = lean_ctor_get(v_decl_2859_, 0);
                v_descr_2863_ = lean_ctor_get(v_decl_2859_, 1);
                v_deprecation_x3f_2864_ = lean_ctor_get(v_decl_2859_, 2);
                v___x_2865_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2866_ = (lean_unbox(v_defValue_2862_) as u8);
                lean_ctor_set_uint8(v___x_2865_, 0 as u32, v___x_2866_);
                lean_inc(v_deprecation_x3f_2864_);
                lean_inc_ref(v_descr_2863_);
                lean_inc_n(v_name_2858_, 2);
                v___x_2867_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2867_, 0, v_name_2858_);
                lean_ctor_set(v___x_2867_, 1, v_ref_2860_);
                lean_ctor_set(v___x_2867_, 2, v___x_2865_);
                lean_ctor_set(v___x_2867_, 3, v_descr_2863_);
                lean_ctor_set(v___x_2867_, 4, v_deprecation_x3f_2864_);
                v___x_2868_ = lean_register_option(v_name_2858_, v___x_2867_);
                if lean_obj_tag(v___x_2868_) == 0 {
                    v_isSharedCheck_2876_ = (!lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2876_ == 0 {
                        v_unused_2877_ = lean_ctor_get(v___x_2868_, 0);
                        lean_dec(v_unused_2877_);
                        v___x_2870_ = v___x_2868_;
                        v_isShared_2871_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2868_);
                        v___x_2870_ = lean_box(0);
                        v_isShared_2871_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_2858_);
                    v_a_2878_ = lean_ctor_get(v___x_2868_, 0);
                    v_isSharedCheck_2885_ = (!lean_is_exclusive(v___x_2868_)) as u8;
                    if v_isSharedCheck_2885_ == 0 {
                        v___x_2880_ = v___x_2868_;
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2878_);
                        lean_dec(v___x_2868_);
                        v___x_2880_ = lean_box(0);
                        v_isShared_2881_ = v_isSharedCheck_2885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_2862_);
                v___x_2872_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2872_, 0, v_name_2858_);
                lean_ctor_set(v___x_2872_, 1, v_defValue_2862_);
                if v_isShared_2871_ == 0 {
                    lean_ctor_set(v___x_2870_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2870_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
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
                    v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
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
    mut v_name_2886_: *mut LeanObject,
    mut v_decl_2887_: *mut LeanObject,
    mut v_ref_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2890_: *mut LeanObject = core::ptr::null_mut();
    v_res_2890_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v_name_2886_, v_decl_2887_, v_ref_2888_);
    lean_dec_ref(v_decl_2887_);
    return v_res_2890_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    v___x_2929_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__1_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2930_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__3_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2931_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn___closed__15_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_;
    v___x_2932_ = l_Lean_Option_register___at___00__private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4__spec__0(v___x_2929_, v___x_2930_, v___x_2931_);
    return v___x_2932_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4____boxed(
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2934_: *mut LeanObject = core::ptr::null_mut();
    v_res_2934_ = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
    return v_res_2934_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(
    mut v_x_2935_: u8,
) -> *mut LeanObject {
    match v_x_2935_ {
        0 => {
            let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
            v___x_2936_ = lean_unsigned_to_nat(0);
            return v___x_2936_;
        }
        1 => {
            let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
            v___x_2937_ = lean_unsigned_to_nat(1);
            return v___x_2937_;
        }
        _ => {
            let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
            v___x_2938_ = lean_unsigned_to_nat(2);
            return v___x_2938_;
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx___boxed(
    mut v_x_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2940_: u8 = 0;
    let mut v_res_2941_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2940_ = (lean_unbox(v_x_2939_) as u8);
    v_res_2941_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_boxed_2940_);
    return v_res_2941_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(
    mut v_x_2942_: u8,
) -> *mut LeanObject {
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    v___x_2943_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorIdx(v_x_2942_);
    return v___x_2943_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx___boxed(
    mut v_x_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2945_: u8 = 0;
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2945_ = (lean_unbox(v_x_2944_) as u8);
    v_res_2946_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toCtorIdx(v_x_4__boxed_2945_);
    return v_res_2946_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(
    mut v_k_2947_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2947_);
    return v_k_2947_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg___boxed(
    mut v_k_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: *mut LeanObject = core::ptr::null_mut();
    v_res_2949_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___redArg(v_k_2948_);
    lean_dec(v_k_2948_);
    return v_res_2949_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(
    mut v_motive_2950_: *mut LeanObject,
    mut v_ctorIdx_2951_: *mut LeanObject,
    mut v_t_2952_: u8,
    mut v_h_2953_: *mut LeanObject,
    mut v_k_2954_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2954_);
    return v_k_2954_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim___boxed(
    mut v_motive_2955_: *mut LeanObject,
    mut v_ctorIdx_2956_: *mut LeanObject,
    mut v_t_2957_: *mut LeanObject,
    mut v_h_2958_: *mut LeanObject,
    mut v_k_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2960_: u8 = 0;
    let mut v_res_2961_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2960_ = (lean_unbox(v_t_2957_) as u8);
    v_res_2961_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_ctorElim(
        v_motive_2955_,
        v_ctorIdx_2956_,
        v_t_boxed_2960_,
        v_h_2958_,
        v_k_2959_,
    );
    lean_dec(v_k_2959_);
    lean_dec(v_ctorIdx_2956_);
    return v_res_2961_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(
    mut v_change_2962_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_change_2962_);
    return v_change_2962_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg___boxed(
    mut v_change_2963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2964_: *mut LeanObject = core::ptr::null_mut();
    v_res_2964_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___redArg(
        v_change_2963_,
    );
    lean_dec(v_change_2963_);
    return v_res_2964_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(
    mut v_motive_2965_: *mut LeanObject,
    mut v_t_2966_: u8,
    mut v_h_2967_: *mut LeanObject,
    mut v_change_2968_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_change_2968_);
    return v_change_2968_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim___boxed(
    mut v_motive_2969_: *mut LeanObject,
    mut v_t_2970_: *mut LeanObject,
    mut v_h_2971_: *mut LeanObject,
    mut v_change_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2973_: u8 = 0;
    let mut v_res_2974_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2973_ = (lean_unbox(v_t_2970_) as u8);
    v_res_2974_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_change_elim(
        v_motive_2969_,
        v_t_boxed_2973_,
        v_h_2971_,
        v_change_2972_,
    );
    lean_dec(v_change_2972_);
    return v_res_2974_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(
    mut v_delete_2975_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_delete_2975_);
    return v_delete_2975_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg___boxed(
    mut v_delete_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2977_: *mut LeanObject = core::ptr::null_mut();
    v_res_2977_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___redArg(
        v_delete_2976_,
    );
    lean_dec(v_delete_2976_);
    return v_res_2977_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(
    mut v_motive_2978_: *mut LeanObject,
    mut v_t_2979_: u8,
    mut v_h_2980_: *mut LeanObject,
    mut v_delete_2981_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_delete_2981_);
    return v_delete_2981_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim___boxed(
    mut v_motive_2982_: *mut LeanObject,
    mut v_t_2983_: *mut LeanObject,
    mut v_h_2984_: *mut LeanObject,
    mut v_delete_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2986_: u8 = 0;
    let mut v_res_2987_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2986_ = (lean_unbox(v_t_2983_) as u8);
    v_res_2987_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_delete_elim(
        v_motive_2982_,
        v_t_boxed_2986_,
        v_h_2984_,
        v_delete_2985_,
    );
    lean_dec(v_delete_2985_);
    return v_res_2987_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(
    mut v_insert_2988_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_insert_2988_);
    return v_insert_2988_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg___boxed(
    mut v_insert_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2990_: *mut LeanObject = core::ptr::null_mut();
    v_res_2990_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___redArg(
        v_insert_2989_,
    );
    lean_dec(v_insert_2989_);
    return v_res_2990_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(
    mut v_motive_2991_: *mut LeanObject,
    mut v_t_2992_: u8,
    mut v_h_2993_: *mut LeanObject,
    mut v_insert_2994_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_insert_2994_);
    return v_insert_2994_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim___boxed(
    mut v_motive_2995_: *mut LeanObject,
    mut v_t_2996_: *mut LeanObject,
    mut v_h_2997_: *mut LeanObject,
    mut v_insert_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2999_: u8 = 0;
    let mut v_res_3000_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2999_ = (lean_unbox(v_t_2996_) as u8);
    v_res_3000_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_insert_elim(
        v_motive_2995_,
        v_t_boxed_2999_,
        v_h_2997_,
        v_insert_2998_,
    );
    lean_dec(v_insert_2998_);
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
    mut v_x_3009_: *mut LeanObject,
    mut v_x_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_49__boxed_3011_: u8 = 0;
    let mut v_x_50__boxed_3012_: u8 = 0;
    let mut v_res_3013_: u8 = 0;
    let mut v_r_3014_: *mut LeanObject = core::ptr::null_mut();
    v_x_49__boxed_3011_ = (lean_unbox(v_x_3009_) as u8);
    v_x_50__boxed_3012_ = (lean_unbox(v_x_3010_) as u8);
    v_res_3013_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(
        v_x_49__boxed_3011_,
        v_x_50__boxed_3012_,
    );
    v_r_3014_ = lean_box((v_res_3013_) as usize);
    return v_r_3014_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(
    mut v_x_3018_: u8,
) -> *mut LeanObject {
    match v_x_3018_ {
        0 => {
            let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
            v___x_3019_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__0;
            return v___x_3019_;
        }
        1 => {
            let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
            v___x_3020_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__1;
            return v___x_3020_;
        }
        _ => {
            let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
            v___x_3021_ =
                l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___closed__2;
            return v___x_3021_;
        }
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString___boxed(
    mut v_x_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_31__boxed_3023_: u8 = 0;
    let mut v_res_3024_: *mut LeanObject = core::ptr::null_mut();
    v_x_31__boxed_3023_ = (lean_unbox(v_x_3022_) as u8);
    v_res_3024_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v_x_31__boxed_3023_);
    return v_res_3024_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(
    mut v_x_3030_: *mut LeanObject,
    mut v_y_3031_: *mut LeanObject,
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
    mut v_x_3037_: *mut LeanObject,
    mut v_y_3038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3039_: u8 = 0;
    let mut v_r_3040_: *mut LeanObject = core::ptr::null_mut();
    v_res_3039_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__0(
        v_x_3037_, v_y_3038_,
    );
    lean_dec(v_y_3038_);
    lean_dec(v_x_3037_);
    v_r_3040_ = lean_box((v_res_3039_) as usize);
    return v_r_3040_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(
    mut v_b_u2082_3041_: u8,
    mut v_x_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    v___x_3043_ = lean_box((v_b_u2082_3041_) as usize);
    v___x_3044_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3044_, 0, v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed(
    mut v_b_u2082_3045_: *mut LeanObject,
    mut v_x_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2082_boxed_3047_: u8 = 0;
    let mut v_res_3048_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3047_ = (lean_unbox(v_b_u2082_3045_) as u8);
    v_res_3048_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1(
        v_b_u2082_boxed_3047_,
        v_x_3046_,
    );
    lean_dec(v_x_3046_);
    return v_res_3048_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(
    mut v___f_3049_: *mut LeanObject,
    mut v_t_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_b_u2082_3052_: u8,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    v___x_3053_ = lean_box((v_b_u2082_3052_) as usize);
    v___f_3054_ = lean_alloc_closure(
        l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3054_, 0, v___x_3053_);
    v___x_3055_ = l_Std_DTreeMap_Internal_Impl_Const_alter___redArg(
        v___f_3049_,
        v_a_3051_,
        v___f_3054_,
        v_t_3050_,
    );
    return v___x_3055_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2___boxed(
    mut v___f_3056_: *mut LeanObject,
    mut v_t_3057_: *mut LeanObject,
    mut v_a_3058_: *mut LeanObject,
    mut v_b_u2082_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2082_boxed_3060_: u8 = 0;
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3060_ = (lean_unbox(v_b_u2082_3059_) as u8);
    v_res_3061_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__2(
        v___f_3056_,
        v_t_3057_,
        v_a_3058_,
        v_b_u2082_boxed_3060_,
    );
    return v_res_3061_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instAppendExprDiff___lam__5(
    mut v___f_3062_: *mut LeanObject,
    mut v___f_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_b_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_changesBefore_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3066_ = lean_ctor_get(v_a_3064_, 0);
                lean_inc(v_changesBefore_3066_);
                v_changesAfter_3067_ = lean_ctor_get(v_a_3064_, 1);
                lean_inc(v_changesAfter_3067_);
                lean_dec_ref(v_a_3064_);
                v_changesBefore_3068_ = lean_ctor_get(v_b_3065_, 0);
                v_changesAfter_3069_ = lean_ctor_get(v_b_3065_, 1);
                v_isSharedCheck_3078_ = (!lean_is_exclusive(v_b_3065_)) as u8;
                if v_isSharedCheck_3078_ == 0 {
                    v___x_3071_ = v_b_3065_;
                    v_isShared_3072_ = v_isSharedCheck_3078_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_changesAfter_3069_);
                    lean_inc(v_changesBefore_3068_);
                    lean_dec(v_b_3065_);
                    v___x_3071_ = lean_box(0);
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
                    lean_ctor_set(v___x_3071_, 1, v___x_3074_);
                    lean_ctor_set(v___x_3071_, 0, v___x_3073_);
                    v___x_3076_ = v___x_3071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
                    lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3074_);
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
    mut v_x_3088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3089_ = lean_ctor_get(v_x_3088_, 0);
    v_snd_3090_ = lean_ctor_get(v_x_3088_, 1);
    v___x_3091_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__0;
    v___x_3092_ = l_Lean_SubExpr_Pos_toString(v_fst_3089_);
    v___x_3093_ = lean_string_append(v___x_3091_, v___x_3092_);
    lean_dec_ref(v___x_3092_);
    v___x_3094_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__1;
    v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
    v___x_3096_ = (lean_unbox(v_snd_3090_) as u8);
    v___x_3097_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toString(v___x_3096_);
    v___x_3098_ = lean_string_append(v___x_3095_, v___x_3097_);
    lean_dec_ref(v___x_3097_);
    v___x_3099_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___closed__2;
    v___x_3100_ = lean_string_append(v___x_3098_, v___x_3099_);
    return v___x_3100_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0___boxed(
    mut v_x_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3102_: *mut LeanObject = core::ptr::null_mut();
    v_res_3102_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__0(v_x_3101_);
    lean_dec_ref(v_x_3101_);
    return v_res_3102_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(
    mut v_x1_3103_: *mut LeanObject,
    mut v_x2_3104_: u8,
    mut v_x3_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3106_ = lean_box((v_x2_3104_) as usize);
    v___x_3107_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3107_, 0, v_x1_3103_);
    lean_ctor_set(v___x_3107_, 1, v___x_3106_);
    v___x_3108_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3108_, 0, v___x_3107_);
    lean_ctor_set(v___x_3108_, 1, v_x3_3105_);
    return v___x_3108_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1___boxed(
    mut v_x1_3109_: *mut LeanObject,
    mut v_x2_3110_: *mut LeanObject,
    mut v_x3_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x2_243__boxed_3112_: u8 = 0;
    let mut v_res_3113_: *mut LeanObject = core::ptr::null_mut();
    v_x2_243__boxed_3112_ = (lean_unbox(v_x2_3110_) as u8);
    v_res_3113_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__1(
        v_x1_3109_,
        v_x2_243__boxed_3112_,
        v_x3_3111_,
    );
    return v_res_3113_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__2(
    mut v___f_3133_: *mut LeanObject,
    mut v___f_3134_: *mut LeanObject,
    mut v_p_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    v___x_3136_ = lean_box(0);
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
    mut v_f_3142_: *mut LeanObject,
    mut v___f_3143_: *mut LeanObject,
    mut v_x_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_changesBefore_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v_changesBefore_3145_ = lean_ctor_get(v_x_3144_, 0);
    lean_inc(v_changesBefore_3145_);
    v_changesAfter_3146_ = lean_ctor_get(v_x_3144_, 1);
    lean_inc(v_changesAfter_3146_);
    lean_dec_ref(v_x_3144_);
    v___x_3147_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__0;
    lean_inc_ref(v_f_3142_);
    v___x_3148_ = lean_apply_1(v_f_3142_, v_changesBefore_3145_);
    lean_inc_ref(v___f_3143_);
    v___x_3149_ = l_List_toString___redArg(v___f_3143_, v___x_3148_);
    v___x_3150_ = lean_string_append(v___x_3147_, v___x_3149_);
    lean_dec_ref(v___x_3149_);
    v___x_3151_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_instToStringExprDiff___lam__3___closed__1;
    v___x_3152_ = lean_string_append(v___x_3150_, v___x_3151_);
    v___x_3153_ = lean_apply_1(v_f_3142_, v_changesAfter_3146_);
    v___x_3154_ = l_List_toString___redArg(v___f_3143_, v___x_3153_);
    v___x_3155_ = lean_string_append(v___x_3152_, v___x_3154_);
    lean_dec_ref(v___x_3154_);
    return v___x_3155_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(
    mut v_k_3166_: *mut LeanObject,
    mut v_v_3167_: *mut LeanObject,
    mut v_t_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: u8 = 0;
    let mut v_impl_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v_size_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3209_: u8 = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3234_: u8 = 0;
    let mut v_unused_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3251_: u8 = 0;
    let mut v_unused_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3258_: u8 = 0;
    let mut v_unused_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v_k_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3275_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_unused_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v_unused_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_unused_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: u8 = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3335_: u8 = 0;
    let mut v_size_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut v_unused_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v_unused_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3398_: u8 = 0;
    let mut v_unused_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3418_: u8 = 0;
    let mut v_unused_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v_k_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_unused_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_unused_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3168_) == 0 {
                    v_size_3169_ = lean_ctor_get(v_t_3168_, 0);
                    v_k_3170_ = lean_ctor_get(v_t_3168_, 1);
                    v_v_3171_ = lean_ctor_get(v_t_3168_, 2);
                    v_l_3172_ = lean_ctor_get(v_t_3168_, 3);
                    v_r_3173_ = lean_ctor_get(v_t_3168_, 4);
                    v_isSharedCheck_3454_ = (!lean_is_exclusive(v_t_3168_)) as u8;
                    if v_isSharedCheck_3454_ == 0 {
                        v___x_3175_ = v_t_3168_;
                        v_isShared_3176_ = v_isSharedCheck_3454_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3173_);
                        lean_inc(v_l_3172_);
                        lean_inc(v_v_3171_);
                        lean_inc(v_k_3170_);
                        lean_inc(v_size_3169_);
                        lean_dec(v_t_3168_);
                        v___x_3175_ = lean_box(0);
                        v_isShared_3176_ = v_isSharedCheck_3454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3455_ = lean_unsigned_to_nat(1);
                    v___x_3456_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3456_, 0, v___x_3455_);
                    lean_ctor_set(v___x_3456_, 1, v_k_3166_);
                    lean_ctor_set(v___x_3456_, 2, v_v_3167_);
                    lean_ctor_set(v___x_3456_, 3, v_t_3168_);
                    lean_ctor_set(v___x_3456_, 4, v_t_3168_);
                    return v___x_3456_;
                }
            }
            1 => {
                v___x_3177_ = lean_nat_dec_lt(v_k_3166_, v_k_3170_);
                if v___x_3177_ == 0 {
                    v___x_3178_ = lean_nat_dec_eq(v_k_3166_, v_k_3170_);
                    if v___x_3178_ == 0 {
                        lean_dec(v_size_3169_);
                        v_impl_3179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3166_, v_v_3167_, v_r_3173_);
                        v___x_3180_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_3172_) == 0 {
                            v_size_3181_ = lean_ctor_get(v_l_3172_, 0);
                            v_size_3182_ = lean_ctor_get(v_impl_3179_, 0);
                            lean_inc(v_size_3182_);
                            v_k_3183_ = lean_ctor_get(v_impl_3179_, 1);
                            lean_inc(v_k_3183_);
                            v_v_3184_ = lean_ctor_get(v_impl_3179_, 2);
                            lean_inc(v_v_3184_);
                            v_l_3185_ = lean_ctor_get(v_impl_3179_, 3);
                            lean_inc(v_l_3185_);
                            v_r_3186_ = lean_ctor_get(v_impl_3179_, 4);
                            lean_inc(v_r_3186_);
                            v___x_3187_ = lean_unsigned_to_nat(3);
                            v___x_3188_ = lean_nat_mul(v___x_3187_, v_size_3181_);
                            v___x_3189_ = lean_nat_dec_lt(v___x_3188_, v_size_3182_);
                            lean_dec(v___x_3188_);
                            if v___x_3189_ == 0 {
                                lean_dec(v_r_3186_);
                                lean_dec(v_l_3185_);
                                lean_dec(v_v_3184_);
                                lean_dec(v_k_3183_);
                                v___x_3190_ = lean_nat_add(v___x_3180_, v_size_3181_);
                                v___x_3191_ = lean_nat_add(v___x_3190_, v_size_3182_);
                                lean_dec(v_size_3182_);
                                lean_dec(v___x_3190_);
                                if v_isShared_3176_ == 0 {
                                    lean_ctor_set(v___x_3175_, 4, v_impl_3179_);
                                    lean_ctor_set(v___x_3175_, 0, v___x_3191_);
                                    v___x_3193_ = v___x_3175_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
                                    lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_k_3170_);
                                    lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_v_3171_);
                                    lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_l_3172_);
                                    lean_ctor_set(v_reuseFailAlloc_3194_, 4, v_impl_3179_);
                                    v___x_3193_ = v_reuseFailAlloc_3194_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3258_ = (!lean_is_exclusive(v_impl_3179_)) as u8;
                                if v_isSharedCheck_3258_ == 0 {
                                    v_unused_3259_ = lean_ctor_get(v_impl_3179_, 4);
                                    lean_dec(v_unused_3259_);
                                    v_unused_3260_ = lean_ctor_get(v_impl_3179_, 3);
                                    lean_dec(v_unused_3260_);
                                    v_unused_3261_ = lean_ctor_get(v_impl_3179_, 2);
                                    lean_dec(v_unused_3261_);
                                    v_unused_3262_ = lean_ctor_get(v_impl_3179_, 1);
                                    lean_dec(v_unused_3262_);
                                    v_unused_3263_ = lean_ctor_get(v_impl_3179_, 0);
                                    lean_dec(v_unused_3263_);
                                    v___x_3196_ = v_impl_3179_;
                                    v_isShared_3197_ = v_isSharedCheck_3258_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_3179_);
                                    v___x_3196_ = lean_box(0);
                                    v_isShared_3197_ = v_isSharedCheck_3258_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3264_ = lean_ctor_get(v_impl_3179_, 3);
                            lean_inc(v_l_3264_);
                            if lean_obj_tag(v_l_3264_) == 0 {
                                v_r_3265_ = lean_ctor_get(v_impl_3179_, 4);
                                v_k_3266_ = lean_ctor_get(v_impl_3179_, 1);
                                v_v_3267_ = lean_ctor_get(v_impl_3179_, 2);
                                v_isSharedCheck_3290_ = (!lean_is_exclusive(v_impl_3179_)) as u8;
                                if v_isSharedCheck_3290_ == 0 {
                                    v_unused_3291_ = lean_ctor_get(v_impl_3179_, 3);
                                    lean_dec(v_unused_3291_);
                                    v_unused_3292_ = lean_ctor_get(v_impl_3179_, 0);
                                    lean_dec(v_unused_3292_);
                                    v___x_3269_ = v_impl_3179_;
                                    v_isShared_3270_ = v_isSharedCheck_3290_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_3265_);
                                    lean_inc(v_v_3267_);
                                    lean_inc(v_k_3266_);
                                    lean_dec(v_impl_3179_);
                                    v___x_3269_ = lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3290_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_3293_ = lean_ctor_get(v_impl_3179_, 4);
                                lean_inc(v_r_3293_);
                                if lean_obj_tag(v_r_3293_) == 0 {
                                    v_k_3294_ = lean_ctor_get(v_impl_3179_, 1);
                                    v_v_3295_ = lean_ctor_get(v_impl_3179_, 2);
                                    v_isSharedCheck_3306_ =
                                        (!lean_is_exclusive(v_impl_3179_)) as u8;
                                    if v_isSharedCheck_3306_ == 0 {
                                        v_unused_3307_ = lean_ctor_get(v_impl_3179_, 4);
                                        lean_dec(v_unused_3307_);
                                        v_unused_3308_ = lean_ctor_get(v_impl_3179_, 3);
                                        lean_dec(v_unused_3308_);
                                        v_unused_3309_ = lean_ctor_get(v_impl_3179_, 0);
                                        lean_dec(v_unused_3309_);
                                        v___x_3297_ = v_impl_3179_;
                                        v_isShared_3298_ = v_isSharedCheck_3306_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3295_);
                                        lean_inc(v_k_3294_);
                                        lean_dec(v_impl_3179_);
                                        v___x_3297_ = lean_box(0);
                                        v_isShared_3298_ = v_isSharedCheck_3306_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_3310_ = lean_unsigned_to_nat(2);
                                    if v_isShared_3176_ == 0 {
                                        lean_ctor_set(v___x_3175_, 4, v_impl_3179_);
                                        lean_ctor_set(v___x_3175_, 3, v_r_3293_);
                                        lean_ctor_set(v___x_3175_, 0, v___x_3310_);
                                        v___x_3312_ = v___x_3175_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
                                        lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3170_);
                                        lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3171_);
                                        lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_r_3293_);
                                        lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_impl_3179_);
                                        v___x_3312_ = v_reuseFailAlloc_3313_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_3171_);
                        lean_dec(v_k_3170_);
                        if v_isShared_3176_ == 0 {
                            lean_ctor_set(v___x_3175_, 2, v_v_3167_);
                            lean_ctor_set(v___x_3175_, 1, v_k_3166_);
                            v___x_3315_ = v___x_3175_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_size_3169_);
                            lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_k_3166_);
                            lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_v_3167_);
                            lean_ctor_set(v_reuseFailAlloc_3316_, 3, v_l_3172_);
                            lean_ctor_set(v_reuseFailAlloc_3316_, 4, v_r_3173_);
                            v___x_3315_ = v_reuseFailAlloc_3316_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_3169_);
                    v_impl_3317_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3166_, v_v_3167_, v_l_3172_);
                    v___x_3318_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_3173_) == 0 {
                        v_size_3319_ = lean_ctor_get(v_r_3173_, 0);
                        v_size_3320_ = lean_ctor_get(v_impl_3317_, 0);
                        lean_inc(v_size_3320_);
                        v_k_3321_ = lean_ctor_get(v_impl_3317_, 1);
                        lean_inc(v_k_3321_);
                        v_v_3322_ = lean_ctor_get(v_impl_3317_, 2);
                        lean_inc(v_v_3322_);
                        v_l_3323_ = lean_ctor_get(v_impl_3317_, 3);
                        lean_inc(v_l_3323_);
                        v_r_3324_ = lean_ctor_get(v_impl_3317_, 4);
                        lean_inc(v_r_3324_);
                        v___x_3325_ = lean_unsigned_to_nat(3);
                        v___x_3326_ = lean_nat_mul(v___x_3325_, v_size_3319_);
                        v___x_3327_ = lean_nat_dec_lt(v___x_3326_, v_size_3320_);
                        lean_dec(v___x_3326_);
                        if v___x_3327_ == 0 {
                            lean_dec(v_r_3324_);
                            lean_dec(v_l_3323_);
                            lean_dec(v_v_3322_);
                            lean_dec(v_k_3321_);
                            v___x_3328_ = lean_nat_add(v___x_3318_, v_size_3320_);
                            lean_dec(v_size_3320_);
                            v___x_3329_ = lean_nat_add(v___x_3328_, v_size_3319_);
                            lean_dec(v___x_3328_);
                            if v_isShared_3176_ == 0 {
                                lean_ctor_set(v___x_3175_, 3, v_impl_3317_);
                                lean_ctor_set(v___x_3175_, 0, v___x_3329_);
                                v___x_3331_ = v___x_3175_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                                lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_k_3170_);
                                lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_v_3171_);
                                lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_impl_3317_);
                                lean_ctor_set(v_reuseFailAlloc_3332_, 4, v_r_3173_);
                                v___x_3331_ = v_reuseFailAlloc_3332_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_3398_ = (!lean_is_exclusive(v_impl_3317_)) as u8;
                            if v_isSharedCheck_3398_ == 0 {
                                v_unused_3399_ = lean_ctor_get(v_impl_3317_, 4);
                                lean_dec(v_unused_3399_);
                                v_unused_3400_ = lean_ctor_get(v_impl_3317_, 3);
                                lean_dec(v_unused_3400_);
                                v_unused_3401_ = lean_ctor_get(v_impl_3317_, 2);
                                lean_dec(v_unused_3401_);
                                v_unused_3402_ = lean_ctor_get(v_impl_3317_, 1);
                                lean_dec(v_unused_3402_);
                                v_unused_3403_ = lean_ctor_get(v_impl_3317_, 0);
                                lean_dec(v_unused_3403_);
                                v___x_3334_ = v_impl_3317_;
                                v_isShared_3335_ = v_isSharedCheck_3398_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_3317_);
                                v___x_3334_ = lean_box(0);
                                v_isShared_3335_ = v_isSharedCheck_3398_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_3404_ = lean_ctor_get(v_impl_3317_, 3);
                        lean_inc(v_l_3404_);
                        if lean_obj_tag(v_l_3404_) == 0 {
                            v_r_3405_ = lean_ctor_get(v_impl_3317_, 4);
                            v_k_3406_ = lean_ctor_get(v_impl_3317_, 1);
                            v_v_3407_ = lean_ctor_get(v_impl_3317_, 2);
                            v_isSharedCheck_3418_ = (!lean_is_exclusive(v_impl_3317_)) as u8;
                            if v_isSharedCheck_3418_ == 0 {
                                v_unused_3419_ = lean_ctor_get(v_impl_3317_, 3);
                                lean_dec(v_unused_3419_);
                                v_unused_3420_ = lean_ctor_get(v_impl_3317_, 0);
                                lean_dec(v_unused_3420_);
                                v___x_3409_ = v_impl_3317_;
                                v_isShared_3410_ = v_isSharedCheck_3418_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_3405_);
                                lean_inc(v_v_3407_);
                                lean_inc(v_k_3406_);
                                lean_dec(v_impl_3317_);
                                v___x_3409_ = lean_box(0);
                                v_isShared_3410_ = v_isSharedCheck_3418_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_3421_ = lean_ctor_get(v_impl_3317_, 4);
                            lean_inc(v_r_3421_);
                            if lean_obj_tag(v_r_3421_) == 0 {
                                v_k_3422_ = lean_ctor_get(v_impl_3317_, 1);
                                v_v_3423_ = lean_ctor_get(v_impl_3317_, 2);
                                v_isSharedCheck_3446_ = (!lean_is_exclusive(v_impl_3317_)) as u8;
                                if v_isSharedCheck_3446_ == 0 {
                                    v_unused_3447_ = lean_ctor_get(v_impl_3317_, 4);
                                    lean_dec(v_unused_3447_);
                                    v_unused_3448_ = lean_ctor_get(v_impl_3317_, 3);
                                    lean_dec(v_unused_3448_);
                                    v_unused_3449_ = lean_ctor_get(v_impl_3317_, 0);
                                    lean_dec(v_unused_3449_);
                                    v___x_3425_ = v_impl_3317_;
                                    v_isShared_3426_ = v_isSharedCheck_3446_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_3423_);
                                    lean_inc(v_k_3422_);
                                    lean_dec(v_impl_3317_);
                                    v___x_3425_ = lean_box(0);
                                    v_isShared_3426_ = v_isSharedCheck_3446_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_3450_ = lean_unsigned_to_nat(2);
                                if v_isShared_3176_ == 0 {
                                    lean_ctor_set(v___x_3175_, 4, v_r_3421_);
                                    lean_ctor_set(v___x_3175_, 3, v_impl_3317_);
                                    lean_ctor_set(v___x_3175_, 0, v___x_3450_);
                                    v___x_3452_ = v___x_3175_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
                                    lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3170_);
                                    lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3171_);
                                    lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_impl_3317_);
                                    lean_ctor_set(v_reuseFailAlloc_3453_, 4, v_r_3421_);
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
                v_size_3198_ = lean_ctor_get(v_l_3185_, 0);
                v_k_3199_ = lean_ctor_get(v_l_3185_, 1);
                v_v_3200_ = lean_ctor_get(v_l_3185_, 2);
                v_l_3201_ = lean_ctor_get(v_l_3185_, 3);
                v_r_3202_ = lean_ctor_get(v_l_3185_, 4);
                v_size_3203_ = lean_ctor_get(v_r_3186_, 0);
                v___x_3204_ = lean_unsigned_to_nat(2);
                v___x_3205_ = lean_nat_mul(v___x_3204_, v_size_3203_);
                v___x_3206_ = lean_nat_dec_lt(v_size_3198_, v___x_3205_);
                lean_dec(v___x_3205_);
                if v___x_3206_ == 0 {
                    lean_inc(v_r_3202_);
                    lean_inc(v_l_3201_);
                    lean_inc(v_v_3200_);
                    lean_inc(v_k_3199_);
                    v_isSharedCheck_3234_ = (!lean_is_exclusive(v_l_3185_)) as u8;
                    if v_isSharedCheck_3234_ == 0 {
                        v_unused_3235_ = lean_ctor_get(v_l_3185_, 4);
                        lean_dec(v_unused_3235_);
                        v_unused_3236_ = lean_ctor_get(v_l_3185_, 3);
                        lean_dec(v_unused_3236_);
                        v_unused_3237_ = lean_ctor_get(v_l_3185_, 2);
                        lean_dec(v_unused_3237_);
                        v_unused_3238_ = lean_ctor_get(v_l_3185_, 1);
                        lean_dec(v_unused_3238_);
                        v_unused_3239_ = lean_ctor_get(v_l_3185_, 0);
                        lean_dec(v_unused_3239_);
                        v___x_3208_ = v_l_3185_;
                        v_isShared_3209_ = v_isSharedCheck_3234_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_3185_);
                        v___x_3208_ = lean_box(0);
                        v_isShared_3209_ = v_isSharedCheck_3234_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3175_);
                    v___x_3240_ = lean_nat_add(v___x_3180_, v_size_3181_);
                    v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3182_);
                    lean_dec(v_size_3182_);
                    v___x_3242_ = lean_nat_add(v___x_3240_, v_size_3198_);
                    lean_dec(v___x_3240_);
                    lean_inc_ref(v_l_3172_);
                    if v_isShared_3197_ == 0 {
                        lean_ctor_set(v___x_3196_, 4, v_l_3185_);
                        lean_ctor_set(v___x_3196_, 3, v_l_3172_);
                        lean_ctor_set(v___x_3196_, 2, v_v_3171_);
                        lean_ctor_set(v___x_3196_, 1, v_k_3170_);
                        lean_ctor_set(v___x_3196_, 0, v___x_3242_);
                        v___x_3244_ = v___x_3196_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3242_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_k_3170_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_v_3171_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 3, v_l_3172_);
                        lean_ctor_set(v_reuseFailAlloc_3257_, 4, v_l_3185_);
                        v___x_3244_ = v_reuseFailAlloc_3257_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3210_ = lean_nat_add(v___x_3180_, v_size_3181_);
                v___x_3211_ = lean_nat_add(v___x_3210_, v_size_3182_);
                lean_dec(v_size_3182_);
                if lean_obj_tag(v_l_3201_) == 0 {
                    v_size_3232_ = lean_ctor_get(v_l_3201_, 0);
                    lean_inc(v_size_3232_);
                    v___y_3224_ = v_size_3232_;
                    state = 8;
                    continue;
                } else {
                    v___x_3233_ = lean_unsigned_to_nat(0);
                    v___y_3224_ = v___x_3233_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3216_ = lean_nat_add(v___y_3213_, v___y_3215_);
                lean_dec(v___y_3215_);
                lean_dec(v___y_3213_);
                if v_isShared_3209_ == 0 {
                    lean_ctor_set(v___x_3208_, 4, v_r_3186_);
                    lean_ctor_set(v___x_3208_, 3, v_r_3202_);
                    lean_ctor_set(v___x_3208_, 2, v_v_3184_);
                    lean_ctor_set(v___x_3208_, 1, v_k_3183_);
                    lean_ctor_set(v___x_3208_, 0, v___x_3216_);
                    v___x_3218_ = v___x_3208_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3216_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_k_3183_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 2, v_v_3184_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 3, v_r_3202_);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 4, v_r_3186_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3197_ == 0 {
                    lean_ctor_set(v___x_3196_, 4, v___x_3218_);
                    lean_ctor_set(v___x_3196_, 3, v___y_3214_);
                    lean_ctor_set(v___x_3196_, 2, v_v_3200_);
                    lean_ctor_set(v___x_3196_, 1, v_k_3199_);
                    lean_ctor_set(v___x_3196_, 0, v___x_3211_);
                    v___x_3220_ = v___x_3196_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3211_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3199_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3200_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 3, v___y_3214_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 4, v___x_3218_);
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
                lean_dec(v___y_3224_);
                lean_dec(v___x_3210_);
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v_l_3201_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3225_);
                    v___x_3227_ = v___x_3175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3225_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_l_3172_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_l_3201_);
                    v___x_3227_ = v_reuseFailAlloc_3231_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3228_ = lean_nat_add(v___x_3180_, v_size_3203_);
                if lean_obj_tag(v_r_3202_) == 0 {
                    v_size_3229_ = lean_ctor_get(v_r_3202_, 0);
                    lean_inc(v_size_3229_);
                    v___y_3213_ = v___x_3228_;
                    v___y_3214_ = v___x_3227_;
                    v___y_3215_ = v_size_3229_;
                    state = 5;
                    continue;
                } else {
                    v___x_3230_ = lean_unsigned_to_nat(0);
                    v___y_3213_ = v___x_3228_;
                    v___y_3214_ = v___x_3227_;
                    v___y_3215_ = v___x_3230_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3251_ = (!lean_is_exclusive(v_l_3172_)) as u8;
                if v_isSharedCheck_3251_ == 0 {
                    v_unused_3252_ = lean_ctor_get(v_l_3172_, 4);
                    lean_dec(v_unused_3252_);
                    v_unused_3253_ = lean_ctor_get(v_l_3172_, 3);
                    lean_dec(v_unused_3253_);
                    v_unused_3254_ = lean_ctor_get(v_l_3172_, 2);
                    lean_dec(v_unused_3254_);
                    v_unused_3255_ = lean_ctor_get(v_l_3172_, 1);
                    lean_dec(v_unused_3255_);
                    v_unused_3256_ = lean_ctor_get(v_l_3172_, 0);
                    lean_dec(v_unused_3256_);
                    v___x_3246_ = v_l_3172_;
                    v_isShared_3247_ = v_isSharedCheck_3251_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_3172_);
                    v___x_3246_ = lean_box(0);
                    v_isShared_3247_ = v_isSharedCheck_3251_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3247_ == 0 {
                    lean_ctor_set(v___x_3246_, 4, v_r_3186_);
                    lean_ctor_set(v___x_3246_, 3, v___x_3244_);
                    lean_ctor_set(v___x_3246_, 2, v_v_3184_);
                    lean_ctor_set(v___x_3246_, 1, v_k_3183_);
                    lean_ctor_set(v___x_3246_, 0, v___x_3241_);
                    v___x_3249_ = v___x_3246_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3241_);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_k_3183_);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 2, v_v_3184_);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 3, v___x_3244_);
                    lean_ctor_set(v_reuseFailAlloc_3250_, 4, v_r_3186_);
                    v___x_3249_ = v_reuseFailAlloc_3250_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3249_;
            }
            13 => {
                v_k_3271_ = lean_ctor_get(v_l_3264_, 1);
                v_v_3272_ = lean_ctor_get(v_l_3264_, 2);
                v_isSharedCheck_3286_ = (!lean_is_exclusive(v_l_3264_)) as u8;
                if v_isSharedCheck_3286_ == 0 {
                    v_unused_3287_ = lean_ctor_get(v_l_3264_, 4);
                    lean_dec(v_unused_3287_);
                    v_unused_3288_ = lean_ctor_get(v_l_3264_, 3);
                    lean_dec(v_unused_3288_);
                    v_unused_3289_ = lean_ctor_get(v_l_3264_, 0);
                    lean_dec(v_unused_3289_);
                    v___x_3274_ = v_l_3264_;
                    v_isShared_3275_ = v_isSharedCheck_3286_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_3272_);
                    lean_inc(v_k_3271_);
                    lean_dec(v_l_3264_);
                    v___x_3274_ = lean_box(0);
                    v_isShared_3275_ = v_isSharedCheck_3286_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3276_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3265_, 2);
                if v_isShared_3275_ == 0 {
                    lean_ctor_set(v___x_3274_, 4, v_r_3265_);
                    lean_ctor_set(v___x_3274_, 3, v_r_3265_);
                    lean_ctor_set(v___x_3274_, 2, v_v_3171_);
                    lean_ctor_set(v___x_3274_, 1, v_k_3170_);
                    lean_ctor_set(v___x_3274_, 0, v___x_3180_);
                    v___x_3278_ = v___x_3274_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3180_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 3, v_r_3265_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 4, v_r_3265_);
                    v___x_3278_ = v_reuseFailAlloc_3285_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_3265_);
                if v_isShared_3270_ == 0 {
                    lean_ctor_set(v___x_3269_, 3, v_r_3265_);
                    lean_ctor_set(v___x_3269_, 0, v___x_3180_);
                    v___x_3280_ = v___x_3269_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3180_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 1, v_k_3266_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 2, v_v_3267_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 3, v_r_3265_);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 4, v_r_3265_);
                    v___x_3280_ = v_reuseFailAlloc_3284_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v___x_3280_);
                    lean_ctor_set(v___x_3175_, 3, v___x_3278_);
                    lean_ctor_set(v___x_3175_, 2, v_v_3272_);
                    lean_ctor_set(v___x_3175_, 1, v_k_3271_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3276_);
                    v___x_3282_ = v___x_3175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3276_);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_k_3271_);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 2, v_v_3272_);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 3, v___x_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 4, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3282_;
            }
            18 => {
                v___x_3299_ = lean_unsigned_to_nat(3);
                if v_isShared_3298_ == 0 {
                    lean_ctor_set(v___x_3297_, 4, v_l_3264_);
                    lean_ctor_set(v___x_3297_, 2, v_v_3171_);
                    lean_ctor_set(v___x_3297_, 1, v_k_3170_);
                    lean_ctor_set(v___x_3297_, 0, v___x_3180_);
                    v___x_3301_ = v___x_3297_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3180_);
                    lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_l_3264_);
                    lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_l_3264_);
                    v___x_3301_ = v_reuseFailAlloc_3305_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v_r_3293_);
                    lean_ctor_set(v___x_3175_, 3, v___x_3301_);
                    lean_ctor_set(v___x_3175_, 2, v_v_3295_);
                    lean_ctor_set(v___x_3175_, 1, v_k_3294_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3299_);
                    v___x_3303_ = v___x_3175_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3299_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_k_3294_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_v_3295_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 3, v___x_3301_);
                    lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_r_3293_);
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
                v_size_3336_ = lean_ctor_get(v_l_3323_, 0);
                v_size_3337_ = lean_ctor_get(v_r_3324_, 0);
                v_k_3338_ = lean_ctor_get(v_r_3324_, 1);
                v_v_3339_ = lean_ctor_get(v_r_3324_, 2);
                v_l_3340_ = lean_ctor_get(v_r_3324_, 3);
                v_r_3341_ = lean_ctor_get(v_r_3324_, 4);
                v___x_3342_ = lean_unsigned_to_nat(2);
                v___x_3343_ = lean_nat_mul(v___x_3342_, v_size_3336_);
                v___x_3344_ = lean_nat_dec_lt(v_size_3337_, v___x_3343_);
                lean_dec(v___x_3343_);
                if v___x_3344_ == 0 {
                    lean_inc(v_r_3341_);
                    lean_inc(v_l_3340_);
                    lean_inc(v_v_3339_);
                    lean_inc(v_k_3338_);
                    v_isSharedCheck_3373_ = (!lean_is_exclusive(v_r_3324_)) as u8;
                    if v_isSharedCheck_3373_ == 0 {
                        v_unused_3374_ = lean_ctor_get(v_r_3324_, 4);
                        lean_dec(v_unused_3374_);
                        v_unused_3375_ = lean_ctor_get(v_r_3324_, 3);
                        lean_dec(v_unused_3375_);
                        v_unused_3376_ = lean_ctor_get(v_r_3324_, 2);
                        lean_dec(v_unused_3376_);
                        v_unused_3377_ = lean_ctor_get(v_r_3324_, 1);
                        lean_dec(v_unused_3377_);
                        v_unused_3378_ = lean_ctor_get(v_r_3324_, 0);
                        lean_dec(v_unused_3378_);
                        v___x_3346_ = v_r_3324_;
                        v_isShared_3347_ = v_isSharedCheck_3373_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_3324_);
                        v___x_3346_ = lean_box(0);
                        v_isShared_3347_ = v_isSharedCheck_3373_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3175_);
                    v___x_3379_ = lean_nat_add(v___x_3318_, v_size_3320_);
                    lean_dec(v_size_3320_);
                    v___x_3380_ = lean_nat_add(v___x_3379_, v_size_3319_);
                    lean_dec(v___x_3379_);
                    v___x_3381_ = lean_nat_add(v___x_3318_, v_size_3319_);
                    v___x_3382_ = lean_nat_add(v___x_3381_, v_size_3337_);
                    lean_dec(v___x_3381_);
                    lean_inc_ref(v_r_3173_);
                    if v_isShared_3335_ == 0 {
                        lean_ctor_set(v___x_3334_, 4, v_r_3173_);
                        lean_ctor_set(v___x_3334_, 3, v_r_3324_);
                        lean_ctor_set(v___x_3334_, 2, v_v_3171_);
                        lean_ctor_set(v___x_3334_, 1, v_k_3170_);
                        lean_ctor_set(v___x_3334_, 0, v___x_3382_);
                        v___x_3384_ = v___x_3334_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3382_);
                        lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_k_3170_);
                        lean_ctor_set(v_reuseFailAlloc_3397_, 2, v_v_3171_);
                        lean_ctor_set(v_reuseFailAlloc_3397_, 3, v_r_3324_);
                        lean_ctor_set(v_reuseFailAlloc_3397_, 4, v_r_3173_);
                        v___x_3384_ = v_reuseFailAlloc_3397_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_3348_ = lean_nat_add(v___x_3318_, v_size_3320_);
                lean_dec(v_size_3320_);
                v___x_3349_ = lean_nat_add(v___x_3348_, v_size_3319_);
                lean_dec(v___x_3348_);
                v___x_3361_ = lean_nat_add(v___x_3318_, v_size_3336_);
                if lean_obj_tag(v_l_3340_) == 0 {
                    v_size_3371_ = lean_ctor_get(v_l_3340_, 0);
                    lean_inc(v_size_3371_);
                    v___y_3363_ = v_size_3371_;
                    state = 29;
                    continue;
                } else {
                    v___x_3372_ = lean_unsigned_to_nat(0);
                    v___y_3363_ = v___x_3372_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_3354_ = lean_nat_add(v___y_3352_, v___y_3353_);
                lean_dec(v___y_3353_);
                lean_dec(v___y_3352_);
                if v_isShared_3347_ == 0 {
                    lean_ctor_set(v___x_3346_, 4, v_r_3173_);
                    lean_ctor_set(v___x_3346_, 3, v_r_3341_);
                    lean_ctor_set(v___x_3346_, 2, v_v_3171_);
                    lean_ctor_set(v___x_3346_, 1, v_k_3170_);
                    lean_ctor_set(v___x_3346_, 0, v___x_3354_);
                    v___x_3356_ = v___x_3346_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3354_);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 3, v_r_3341_);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 4, v_r_3173_);
                    v___x_3356_ = v_reuseFailAlloc_3360_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3335_ == 0 {
                    lean_ctor_set(v___x_3334_, 4, v___x_3356_);
                    lean_ctor_set(v___x_3334_, 3, v___y_3351_);
                    lean_ctor_set(v___x_3334_, 2, v_v_3339_);
                    lean_ctor_set(v___x_3334_, 1, v_k_3338_);
                    lean_ctor_set(v___x_3334_, 0, v___x_3349_);
                    v___x_3358_ = v___x_3334_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3349_);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_k_3338_);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 2, v_v_3339_);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 3, v___y_3351_);
                    lean_ctor_set(v_reuseFailAlloc_3359_, 4, v___x_3356_);
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
                lean_dec(v___y_3363_);
                lean_dec(v___x_3361_);
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v_l_3340_);
                    lean_ctor_set(v___x_3175_, 3, v_l_3323_);
                    lean_ctor_set(v___x_3175_, 2, v_v_3322_);
                    lean_ctor_set(v___x_3175_, 1, v_k_3321_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3364_);
                    v___x_3366_ = v___x_3175_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3364_);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_k_3321_);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_v_3322_);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_l_3323_);
                    lean_ctor_set(v_reuseFailAlloc_3370_, 4, v_l_3340_);
                    v___x_3366_ = v_reuseFailAlloc_3370_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_3367_ = lean_nat_add(v___x_3318_, v_size_3319_);
                if lean_obj_tag(v_r_3341_) == 0 {
                    v_size_3368_ = lean_ctor_get(v_r_3341_, 0);
                    lean_inc(v_size_3368_);
                    v___y_3351_ = v___x_3366_;
                    v___y_3352_ = v___x_3367_;
                    v___y_3353_ = v_size_3368_;
                    state = 26;
                    continue;
                } else {
                    v___x_3369_ = lean_unsigned_to_nat(0);
                    v___y_3351_ = v___x_3366_;
                    v___y_3352_ = v___x_3367_;
                    v___y_3353_ = v___x_3369_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3391_ = (!lean_is_exclusive(v_r_3173_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v_unused_3392_ = lean_ctor_get(v_r_3173_, 4);
                    lean_dec(v_unused_3392_);
                    v_unused_3393_ = lean_ctor_get(v_r_3173_, 3);
                    lean_dec(v_unused_3393_);
                    v_unused_3394_ = lean_ctor_get(v_r_3173_, 2);
                    lean_dec(v_unused_3394_);
                    v_unused_3395_ = lean_ctor_get(v_r_3173_, 1);
                    lean_dec(v_unused_3395_);
                    v_unused_3396_ = lean_ctor_get(v_r_3173_, 0);
                    lean_dec(v_unused_3396_);
                    v___x_3386_ = v_r_3173_;
                    v_isShared_3387_ = v_isSharedCheck_3391_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_3173_);
                    v___x_3386_ = lean_box(0);
                    v_isShared_3387_ = v_isSharedCheck_3391_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3387_ == 0 {
                    lean_ctor_set(v___x_3386_, 4, v___x_3384_);
                    lean_ctor_set(v___x_3386_, 3, v_l_3323_);
                    lean_ctor_set(v___x_3386_, 2, v_v_3322_);
                    lean_ctor_set(v___x_3386_, 1, v_k_3321_);
                    lean_ctor_set(v___x_3386_, 0, v___x_3380_);
                    v___x_3389_ = v___x_3386_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3380_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_k_3321_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_v_3322_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_l_3323_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 4, v___x_3384_);
                    v___x_3389_ = v_reuseFailAlloc_3390_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3389_;
            }
            34 => {
                v___x_3411_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_3405_);
                if v_isShared_3410_ == 0 {
                    lean_ctor_set(v___x_3409_, 3, v_r_3405_);
                    lean_ctor_set(v___x_3409_, 2, v_v_3171_);
                    lean_ctor_set(v___x_3409_, 1, v_k_3170_);
                    lean_ctor_set(v___x_3409_, 0, v___x_3318_);
                    v___x_3413_ = v___x_3409_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3318_);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_r_3405_);
                    lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_r_3405_);
                    v___x_3413_ = v_reuseFailAlloc_3417_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v___x_3413_);
                    lean_ctor_set(v___x_3175_, 3, v_l_3404_);
                    lean_ctor_set(v___x_3175_, 2, v_v_3407_);
                    lean_ctor_set(v___x_3175_, 1, v_k_3406_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3411_);
                    v___x_3415_ = v___x_3175_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_k_3406_);
                    lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_v_3407_);
                    lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_l_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3416_, 4, v___x_3413_);
                    v___x_3415_ = v_reuseFailAlloc_3416_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3415_;
            }
            37 => {
                v_k_3427_ = lean_ctor_get(v_r_3421_, 1);
                v_v_3428_ = lean_ctor_get(v_r_3421_, 2);
                v_isSharedCheck_3442_ = (!lean_is_exclusive(v_r_3421_)) as u8;
                if v_isSharedCheck_3442_ == 0 {
                    v_unused_3443_ = lean_ctor_get(v_r_3421_, 4);
                    lean_dec(v_unused_3443_);
                    v_unused_3444_ = lean_ctor_get(v_r_3421_, 3);
                    lean_dec(v_unused_3444_);
                    v_unused_3445_ = lean_ctor_get(v_r_3421_, 0);
                    lean_dec(v_unused_3445_);
                    v___x_3430_ = v_r_3421_;
                    v_isShared_3431_ = v_isSharedCheck_3442_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_3428_);
                    lean_inc(v_k_3427_);
                    lean_dec(v_r_3421_);
                    v___x_3430_ = lean_box(0);
                    v_isShared_3431_ = v_isSharedCheck_3442_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_3432_ = lean_unsigned_to_nat(3);
                if v_isShared_3431_ == 0 {
                    lean_ctor_set(v___x_3430_, 4, v_l_3404_);
                    lean_ctor_set(v___x_3430_, 3, v_l_3404_);
                    lean_ctor_set(v___x_3430_, 2, v_v_3423_);
                    lean_ctor_set(v___x_3430_, 1, v_k_3422_);
                    lean_ctor_set(v___x_3430_, 0, v___x_3318_);
                    v___x_3434_ = v___x_3430_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3318_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_k_3422_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 2, v_v_3423_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 3, v_l_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3441_, 4, v_l_3404_);
                    v___x_3434_ = v_reuseFailAlloc_3441_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_3426_ == 0 {
                    lean_ctor_set(v___x_3425_, 4, v_l_3404_);
                    lean_ctor_set(v___x_3425_, 2, v_v_3171_);
                    lean_ctor_set(v___x_3425_, 1, v_k_3170_);
                    lean_ctor_set(v___x_3425_, 0, v___x_3318_);
                    v___x_3436_ = v___x_3425_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3318_);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_k_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 2, v_v_3171_);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 3, v_l_3404_);
                    lean_ctor_set(v_reuseFailAlloc_3440_, 4, v_l_3404_);
                    v___x_3436_ = v_reuseFailAlloc_3440_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3176_ == 0 {
                    lean_ctor_set(v___x_3175_, 4, v___x_3436_);
                    lean_ctor_set(v___x_3175_, 3, v___x_3434_);
                    lean_ctor_set(v___x_3175_, 2, v_v_3428_);
                    lean_ctor_set(v___x_3175_, 1, v_k_3427_);
                    lean_ctor_set(v___x_3175_, 0, v___x_3432_);
                    v___x_3438_ = v___x_3175_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_k_3427_);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_v_3428_);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 3, v___x_3434_);
                    lean_ctor_set(v_reuseFailAlloc_3439_, 4, v___x_3436_);
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
    mut v_p_3457_: *mut LeanObject,
    mut v_d_3458_: u8,
    mut v_00_u03b4_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_changesBefore_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3460_ = lean_ctor_get(v_00_u03b4_3459_, 0);
                v_changesAfter_3461_ = lean_ctor_get(v_00_u03b4_3459_, 1);
                v_isSharedCheck_3470_ = (!lean_is_exclusive(v_00_u03b4_3459_)) as u8;
                if v_isSharedCheck_3470_ == 0 {
                    v___x_3463_ = v_00_u03b4_3459_;
                    v_isShared_3464_ = v_isSharedCheck_3470_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_changesAfter_3461_);
                    lean_inc(v_changesBefore_3460_);
                    lean_dec(v_00_u03b4_3459_);
                    v___x_3463_ = lean_box(0);
                    v_isShared_3464_ = v_isSharedCheck_3470_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3465_ = lean_box((v_d_3458_) as usize);
                v___x_3466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_3457_, v___x_3465_, v_changesBefore_3460_);
                if v_isShared_3464_ == 0 {
                    lean_ctor_set(v___x_3463_, 0, v___x_3466_);
                    v___x_3468_ = v___x_3463_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_changesAfter_3461_);
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
    mut v_p_3471_: *mut LeanObject,
    mut v_d_3472_: *mut LeanObject,
    mut v_00_u03b4_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_3474_: u8 = 0;
    let mut v_res_3475_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_3474_ = (lean_unbox(v_d_3472_) as u8);
    v_res_3475_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(
        v_p_3471_,
        v_d_boxed_3474_,
        v_00_u03b4_3473_,
    );
    return v_res_3475_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0(
    mut v_00_u03b2_3476_: *mut LeanObject,
    mut v_k_3477_: *mut LeanObject,
    mut v_v_3478_: *mut LeanObject,
    mut v_t_3479_: *mut LeanObject,
    mut v_hl_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_k_3477_, v_v_3478_, v_t_3479_);
    return v___x_3481_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(
    mut v_p_3482_: *mut LeanObject,
    mut v_d_3483_: u8,
    mut v_00_u03b4_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_changesBefore_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_changesBefore_3485_ = lean_ctor_get(v_00_u03b4_3484_, 0);
                v_changesAfter_3486_ = lean_ctor_get(v_00_u03b4_3484_, 1);
                v_isSharedCheck_3495_ = (!lean_is_exclusive(v_00_u03b4_3484_)) as u8;
                if v_isSharedCheck_3495_ == 0 {
                    v___x_3488_ = v_00_u03b4_3484_;
                    v_isShared_3489_ = v_isSharedCheck_3495_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_changesAfter_3486_);
                    lean_inc(v_changesBefore_3485_);
                    lean_dec(v_00_u03b4_3484_);
                    v___x_3488_ = lean_box(0);
                    v_isShared_3489_ = v_isSharedCheck_3495_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3490_ = lean_box((v_d_3483_) as usize);
                v___x_3491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_p_3482_, v___x_3490_, v_changesAfter_3486_);
                if v_isShared_3489_ == 0 {
                    lean_ctor_set(v___x_3488_, 1, v___x_3491_);
                    v___x_3493_ = v___x_3488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_changesBefore_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3491_);
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
    mut v_p_3496_: *mut LeanObject,
    mut v_d_3497_: *mut LeanObject,
    mut v_00_u03b4_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_3499_ = (lean_unbox(v_d_3497_) as u8);
    v_res_3500_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertAfterChange(
        v_p_3496_,
        v_d_boxed_3499_,
        v_00_u03b4_3498_,
    );
    return v_res_3500_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
    mut v_before_3501_: *mut LeanObject,
    mut v_after_3502_: *mut LeanObject,
    mut v_d_3503_: u8,
) -> *mut LeanObject {
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ = lean_box(1);
    v___x_3505_ = lean_box((v_d_3503_) as usize);
    v___x_3506_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_before_3501_, v___x_3505_, v___x_3504_);
    v___x_3507_ = lean_box((v_d_3503_) as usize);
    v___x_3508_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange_spec__0___redArg(v_after_3502_, v___x_3507_, v___x_3504_);
    v___x_3509_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3509_, 0, v___x_3506_);
    lean_ctor_set(v___x_3509_, 1, v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos___boxed(
    mut v_before_3510_: *mut LeanObject,
    mut v_after_3511_: *mut LeanObject,
    mut v_d_3512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_3513_: u8 = 0;
    let mut v_res_3514_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_3513_ = (lean_unbox(v_d_3512_) as u8);
    v_res_3514_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
        v_before_3510_,
        v_after_3511_,
        v_d_boxed_3513_,
    );
    return v_res_3514_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
    mut v_before_3515_: *mut LeanObject,
    mut v_after_3516_: *mut LeanObject,
    mut v_d_3517_: u8,
) -> *mut LeanObject {
    let mut v_pos_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    v_pos_3518_ = lean_ctor_get(v_before_3515_, 1);
    lean_inc(v_pos_3518_);
    lean_dec_ref(v_before_3515_);
    v_pos_3519_ = lean_ctor_get(v_after_3516_, 1);
    lean_inc(v_pos_3519_);
    lean_dec_ref(v_after_3516_);
    v___x_3520_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
        v_pos_3518_,
        v_pos_3519_,
        v_d_3517_,
    );
    return v___x_3520_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange___boxed(
    mut v_before_3521_: *mut LeanObject,
    mut v_after_3522_: *mut LeanObject,
    mut v_d_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_boxed_3524_: u8 = 0;
    let mut v_res_3525_: *mut LeanObject = core::ptr::null_mut();
    v_d_boxed_3524_ = (lean_unbox(v_d_3523_) as u8);
    v_res_3525_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
        v_before_3521_,
        v_after_3522_,
        v_d_boxed_3524_,
    );
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(
    mut v_d_3526_: *mut LeanObject,
) -> u8 {
    let mut v_changesAfter_3527_: *mut LeanObject = core::ptr::null_mut();
    v_changesAfter_3527_ = lean_ctor_get(v_d_3526_, 1);
    if lean_obj_tag(v_changesAfter_3527_) == 0 {
        let mut v___x_3528_: u8 = 0;
        v___x_3528_ = 0;
        return v___x_3528_;
    } else {
        let mut v_changesBefore_3529_: *mut LeanObject = core::ptr::null_mut();
        v_changesBefore_3529_ = lean_ctor_get(v_d_3526_, 0);
        if lean_obj_tag(v_changesBefore_3529_) == 0 {
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
    mut v_d_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3533_: u8 = 0;
    let mut v_r_3534_: *mut LeanObject = core::ptr::null_mut();
    v_res_3533_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_d_3532_);
    lean_dec_ref(v_d_3532_);
    v_r_3534_ = lean_box((v_res_3533_) as usize);
    return v_r_3534_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(
    mut v_k_3535_: *mut LeanObject,
    mut v_b_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3540_);
    lean_inc_ref(v___y_3539_);
    lean_inc(v___y_3538_);
    lean_inc_ref(v___y_3537_);
    v___x_3542_ = lean_apply_6(
        v_k_3535_,
        v_b_3536_,
        v___y_3537_,
        v___y_3538_,
        v___y_3539_,
        v___y_3540_,
        lean_box(0),
    );
    return v___x_3542_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed(
    mut v_k_3543_: *mut LeanObject,
    mut v_b_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
    mut v___y_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3550_: *mut LeanObject = core::ptr::null_mut();
    v_res_3550_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0(v_k_3543_, v_b_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
    lean_dec(v___y_3548_);
    lean_dec_ref(v___y_3547_);
    lean_dec(v___y_3546_);
    lean_dec_ref(v___y_3545_);
    return v_res_3550_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(
    mut v_name_3551_: *mut LeanObject,
    mut v_bi_3552_: u8,
    mut v_type_3553_: *mut LeanObject,
    mut v_k_3554_: *mut LeanObject,
    mut v_kind_3555_: u8,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_a_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3561_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_3561_, 0, v_k_3554_);
                v___x_3562_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3562_) == 0 {
                    v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3570_ = (!lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3562_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3563_);
                        lean_dec(v___x_3562_);
                        v___x_3565_ = lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3571_ = lean_ctor_get(v___x_3562_, 0);
                    v_isSharedCheck_3578_ = (!lean_is_exclusive(v___x_3562_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v___x_3573_ = v___x_3562_;
                        v_isShared_3574_ = v_isSharedCheck_3578_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3571_);
                        lean_dec(v___x_3562_);
                        v___x_3573_ = lean_box(0);
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
                    v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
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
                    v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
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
    mut v_name_3579_: *mut LeanObject,
    mut v_bi_3580_: *mut LeanObject,
    mut v_type_3581_: *mut LeanObject,
    mut v_k_3582_: *mut LeanObject,
    mut v_kind_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3589_: u8 = 0;
    let mut v_kind_boxed_3590_: u8 = 0;
    let mut v_res_3591_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3589_ = (lean_unbox(v_bi_3580_) as u8);
    v_kind_boxed_3590_ = (lean_unbox(v_kind_3583_) as u8);
    v_res_3591_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_3579_, v_bi_boxed_3589_, v_type_3581_, v_k_3582_, v_kind_boxed_3590_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
    lean_dec(v___y_3587_);
    lean_dec_ref(v___y_3586_);
    lean_dec(v___y_3585_);
    lean_dec_ref(v___y_3584_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(
    mut v_00_u03b1_3592_: *mut LeanObject,
    mut v_name_3593_: *mut LeanObject,
    mut v_bi_3594_: u8,
    mut v_type_3595_: *mut LeanObject,
    mut v_k_3596_: *mut LeanObject,
    mut v_kind_3597_: u8,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_name_3593_, v_bi_3594_, v_type_3595_, v_k_3596_, v_kind_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___boxed(
    mut v_00_u03b1_3604_: *mut LeanObject,
    mut v_name_3605_: *mut LeanObject,
    mut v_bi_3606_: *mut LeanObject,
    mut v_type_3607_: *mut LeanObject,
    mut v_k_3608_: *mut LeanObject,
    mut v_kind_3609_: *mut LeanObject,
    mut v___y_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
    mut v___y_3613_: *mut LeanObject,
    mut v___y_3614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3615_: u8 = 0;
    let mut v_kind_boxed_3616_: u8 = 0;
    let mut v_res_3617_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3615_ = (lean_unbox(v_bi_3606_) as u8);
    v_kind_boxed_3616_ = (lean_unbox(v_kind_3609_) as u8);
    v_res_3617_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6(v_00_u03b1_3604_, v_name_3605_, v_bi_boxed_3615_, v_type_3607_, v_k_3608_, v_kind_boxed_3616_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
    lean_dec(v___y_3613_);
    lean_dec_ref(v___y_3612_);
    lean_dec(v___y_3611_);
    lean_dec_ref(v___y_3610_);
    return v_res_3617_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(
    mut v_msgData_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    v___x_3624_ = lean_st_ref_get(v___y_3622_);
    v_env_3625_ = lean_ctor_get(v___x_3624_, 0);
    lean_inc_ref(v_env_3625_);
    lean_dec(v___x_3624_);
    v___x_3626_ = lean_st_ref_get(v___y_3620_);
    v_mctx_3627_ = lean_ctor_get(v___x_3626_, 0);
    lean_inc_ref(v_mctx_3627_);
    lean_dec(v___x_3626_);
    v_lctx_3628_ = lean_ctor_get(v___y_3619_, 2);
    v_options_3629_ = lean_ctor_get(v___y_3621_, 2);
    lean_inc_ref(v_options_3629_);
    lean_inc_ref(v_lctx_3628_);
    v___x_3630_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3630_, 0, v_env_3625_);
    lean_ctor_set(v___x_3630_, 1, v_mctx_3627_);
    lean_ctor_set(v___x_3630_, 2, v_lctx_3628_);
    lean_ctor_set(v___x_3630_, 3, v_options_3629_);
    v___x_3631_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3631_, 0, v___x_3630_);
    lean_ctor_set(v___x_3631_, 1, v_msgData_3618_);
    v___x_3632_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3632_, 0, v___x_3631_);
    return v___x_3632_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4___boxed(
    mut v_msgData_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3639_: *mut LeanObject = core::ptr::null_mut();
    v_res_3639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msgData_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
    lean_dec(v___y_3637_);
    lean_dec_ref(v___y_3636_);
    lean_dec(v___y_3635_);
    lean_dec_ref(v___y_3634_);
    return v_res_3639_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(
    mut v_msg_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3646_ = lean_ctor_get(v___y_3643_, 5);
                v___x_3647_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3_spec__4(v_msg_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
                v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
                v_isSharedCheck_3656_ = (!lean_is_exclusive(v___x_3647_)) as u8;
                if v_isSharedCheck_3656_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    v_isShared_3651_ = v_isSharedCheck_3656_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3648_);
                    lean_dec(v___x_3647_);
                    v___x_3650_ = lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3656_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3646_);
                v___x_3652_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3652_, 0, v_ref_3646_);
                lean_ctor_set(v___x_3652_, 1, v_a_3648_);
                if v_isShared_3651_ == 0 {
                    lean_ctor_set_tag(v___x_3650_, 1);
                    lean_ctor_set(v___x_3650_, 0, v___x_3652_);
                    v___x_3654_ = v___x_3650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
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
    mut v_msg_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
    mut v___y_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3663_: *mut LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
    lean_dec(v___y_3661_);
    lean_dec_ref(v___y_3660_);
    lean_dec(v___y_3659_);
    lean_dec_ref(v___y_3658_);
    return v_res_3663_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(
    mut v_x_3664_: *mut LeanObject,
    mut v_x_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3664_) == 0 {
                    v___x_3671_ = l_List_reverse___redArg(v_x_3665_);
                    v___x_3672_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3672_, 0, v___x_3671_);
                    return v___x_3672_;
                } else {
                    v_head_3673_ = lean_ctor_get(v_x_3664_, 0);
                    v_tail_3674_ = lean_ctor_get(v_x_3664_, 1);
                    v_isSharedCheck_3692_ = (!lean_is_exclusive(v_x_3664_)) as u8;
                    if v_isSharedCheck_3692_ == 0 {
                        v___x_3676_ = v_x_3664_;
                        v_isShared_3677_ = v_isSharedCheck_3692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3674_);
                        lean_inc(v_head_3673_);
                        lean_dec(v_x_3664_);
                        v___x_3676_ = lean_box(0);
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
                if lean_obj_tag(v___x_3678_) == 0 {
                    v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
                    lean_inc(v_a_3679_);
                    lean_dec_ref_known(v___x_3678_, 1);
                    if v_isShared_3677_ == 0 {
                        lean_ctor_set(v___x_3676_, 1, v_x_3665_);
                        lean_ctor_set(v___x_3676_, 0, v_a_3679_);
                        v___x_3681_ = v___x_3676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3679_);
                        lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_x_3665_);
                        v___x_3681_ = v_reuseFailAlloc_3683_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3676_);
                    lean_dec(v_tail_3674_);
                    lean_dec(v_x_3665_);
                    v_a_3684_ = lean_ctor_get(v___x_3678_, 0);
                    v_isSharedCheck_3691_ = (!lean_is_exclusive(v___x_3678_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v___x_3686_ = v___x_3678_;
                        v_isShared_3687_ = v_isSharedCheck_3691_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3684_);
                        lean_dec(v___x_3678_);
                        v___x_3686_ = lean_box(0);
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
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_a_3684_);
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
    mut v_x_3693_: *mut LeanObject,
    mut v_x_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
    mut v___y_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3700_: *mut LeanObject = core::ptr::null_mut();
    v_res_3700_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v_x_3693_, v_x_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
    lean_dec(v___y_3698_);
    lean_dec_ref(v___y_3697_);
    lean_dec(v___y_3696_);
    lean_dec_ref(v___y_3695_);
    return v_res_3700_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(
    mut v_upperBound_3701_: *mut LeanObject,
    mut v_before_3702_: *mut LeanObject,
    mut v_a_3703_: *mut LeanObject,
    mut v_b_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3706_: u8 = 0;
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3706_ = lean_nat_dec_lt(v_a_3703_, v_upperBound_3701_);
                if v___x_3706_ == 0 {
                    lean_dec(v_a_3703_);
                    lean_dec_ref(v_before_3702_);
                    v___x_3707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3707_, 0, v_b_3704_);
                    return v___x_3707_;
                } else {
                    v_pos_3708_ = lean_ctor_get(v_before_3702_, 1);
                    lean_inc(v_pos_3708_);
                    lean_inc(v_a_3703_);
                    v___x_3709_ = l_Lean_SubExpr_Pos_pushNthBindingDomain(v_a_3703_, v_pos_3708_);
                    v___x_3710_ = 1;
                    v___x_3711_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_insertBeforeChange(
                            v___x_3709_,
                            v___x_3710_,
                            v_b_3704_,
                        );
                    v___x_3712_ = lean_unsigned_to_nat(1);
                    v___x_3713_ = lean_nat_add(v_a_3703_, v___x_3712_);
                    lean_dec(v_a_3703_);
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
    mut v_upperBound_3715_: *mut LeanObject,
    mut v_before_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
    mut v_b_3718_: *mut LeanObject,
    mut v___y_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3720_: *mut LeanObject = core::ptr::null_mut();
    v_res_3720_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_3715_, v_before_3716_, v_a_3717_, v_b_3718_);
    lean_dec(v_upperBound_3715_);
    return v_res_3720_;
}
pub unsafe fn l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(
    mut v_x_3721_: *mut LeanObject,
    mut v_x_3722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: u8 = 0;
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3721_) == 0 {
                    v___x_3723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3723_, 0, v_x_3722_);
                    return v___x_3723_;
                } else {
                    if lean_obj_tag(v_x_3722_) == 0 {
                        v___x_3724_ = lean_box(0);
                        return v___x_3724_;
                    } else {
                        v_head_3725_ = lean_ctor_get(v_x_3721_, 0);
                        v_tail_3726_ = lean_ctor_get(v_x_3721_, 1);
                        v_head_3727_ = lean_ctor_get(v_x_3722_, 0);
                        lean_inc(v_head_3727_);
                        v_tail_3728_ = lean_ctor_get(v_x_3722_, 1);
                        lean_inc(v_tail_3728_);
                        lean_dec_ref_known(v_x_3722_, 2);
                        v___x_3729_ = lean_name_eq(v_head_3725_, v_head_3727_);
                        lean_dec(v_head_3727_);
                        if v___x_3729_ == 0 {
                            lean_dec(v_tail_3728_);
                            v___x_3730_ = lean_box(0);
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
    mut v_x_3732_: *mut LeanObject,
    mut v_x_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3734_: *mut LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v_x_3732_, v_x_3733_);
    lean_dec(v_x_3732_);
    return v_res_3734_;
}
pub unsafe fn l_List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0(
    mut v_l_u2081_3735_: *mut LeanObject,
    mut v_l_u2082_3736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3737_ = l_List_reverse___redArg(v_l_u2081_3735_);
                v___x_3738_ = l_List_reverse___redArg(v_l_u2082_3736_);
                v___x_3739_ = l_List_isPrefixOf_x3f___at___00List_isSuffixOf_x3f___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__0_spec__0(v___x_3737_, v___x_3738_);
                lean_dec(v___x_3737_);
                if lean_obj_tag(v___x_3739_) == 0 {
                    return v___x_3739_;
                } else {
                    v_val_3740_ = lean_ctor_get(v___x_3739_, 0);
                    v_isSharedCheck_3748_ = (!lean_is_exclusive(v___x_3739_)) as u8;
                    if v_isSharedCheck_3748_ == 0 {
                        v___x_3742_ = v___x_3739_;
                        v_isShared_3743_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3740_);
                        lean_dec(v___x_3739_);
                        v___x_3742_ = lean_box(0);
                        v_isShared_3743_ = v_isSharedCheck_3748_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3744_ = l_List_reverse___redArg(v_val_3740_);
                if v_isShared_3743_ == 0 {
                    lean_ctor_set(v___x_3742_, 0, v___x_3744_);
                    v___x_3746_ = v___x_3742_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
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
    mut v_k_3750_: *mut LeanObject,
    mut v_t_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3759_: u8 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: u8 = 0;
    let mut v_impl_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3751_) == 0 {
                    v_size_3752_ = lean_ctor_get(v_t_3751_, 0);
                    v_k_3753_ = lean_ctor_get(v_t_3751_, 1);
                    v_v_3754_ = lean_ctor_get(v_t_3751_, 2);
                    v_l_3755_ = lean_ctor_get(v_t_3751_, 3);
                    v_r_3756_ = lean_ctor_get(v_t_3751_, 4);
                    v_isSharedCheck_3770_ = (!lean_is_exclusive(v_t_3751_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3758_ = v_t_3751_;
                        v_isShared_3759_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3756_);
                        lean_inc(v_l_3755_);
                        lean_inc(v_v_3754_);
                        lean_inc(v_k_3753_);
                        lean_inc(v_size_3752_);
                        lean_dec(v_t_3751_);
                        v___x_3758_ = lean_box(0);
                        v_isShared_3759_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3771_ = lean_unsigned_to_nat(1);
                    v___x_3772_ = lean_box((v_b_u2082_3749_) as usize);
                    v___x_3773_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3773_, 0, v___x_3771_);
                    lean_ctor_set(v___x_3773_, 1, v_k_3750_);
                    lean_ctor_set(v___x_3773_, 2, v___x_3772_);
                    lean_ctor_set(v___x_3773_, 3, v_t_3751_);
                    lean_ctor_set(v___x_3773_, 4, v_t_3751_);
                    return v___x_3773_;
                }
            }
            1 => {
                v___x_3760_ = lean_nat_dec_lt(v_k_3750_, v_k_3753_);
                if v___x_3760_ == 0 {
                    v___x_3761_ = lean_nat_dec_eq(v_k_3750_, v_k_3753_);
                    if v___x_3761_ == 0 {
                        lean_del_object(v___x_3758_);
                        lean_dec(v_size_3752_);
                        v_impl_3762_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_3749_, v_k_3750_, v_r_3756_);
                        v___x_3763_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_3753_,
                            v_v_3754_,
                            v_l_3755_,
                            v_impl_3762_,
                        );
                        return v___x_3763_;
                    } else {
                        lean_dec(v_v_3754_);
                        lean_dec(v_k_3753_);
                        v___x_3764_ = lean_box((v_b_u2082_3749_) as usize);
                        if v_isShared_3759_ == 0 {
                            lean_ctor_set(v___x_3758_, 2, v___x_3764_);
                            lean_ctor_set(v___x_3758_, 1, v_k_3750_);
                            v___x_3766_ = v___x_3758_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_size_3752_);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_k_3750_);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 2, v___x_3764_);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 3, v_l_3755_);
                            lean_ctor_set(v_reuseFailAlloc_3767_, 4, v_r_3756_);
                            v___x_3766_ = v_reuseFailAlloc_3767_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3758_);
                    lean_dec(v_size_3752_);
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
    mut v_b_u2082_3774_: *mut LeanObject,
    mut v_k_3775_: *mut LeanObject,
    mut v_t_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2082_boxed_3777_: u8 = 0;
    let mut v_res_3778_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_3777_ = (lean_unbox(v_b_u2082_3774_) as u8);
    v_res_3778_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_boxed_3777_, v_k_3775_, v_t_3776_);
    return v_res_3778_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(
    mut v_init_3779_: *mut LeanObject,
    mut v_x_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3780_) == 0 {
                    v_k_3781_ = lean_ctor_get(v_x_3780_, 1);
                    lean_inc(v_k_3781_);
                    v_v_3782_ = lean_ctor_get(v_x_3780_, 2);
                    lean_inc(v_v_3782_);
                    v_l_3783_ = lean_ctor_get(v_x_3780_, 3);
                    lean_inc(v_l_3783_);
                    v_r_3784_ = lean_ctor_get(v_x_3780_, 4);
                    lean_inc(v_r_3784_);
                    lean_dec_ref_known(v_x_3780_, 5);
                    v___x_3785_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_3779_, v_l_3783_);
                    v___x_3786_ = (lean_unbox(v_v_3782_) as u8);
                    lean_dec(v_v_3782_);
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
    mut v_as_3789_: *mut LeanObject,
    mut v_i_3790_: usize,
    mut v_stop_3791_: usize,
    mut v_b_3792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3793_: u8 = 0;
    let mut v_changesBefore_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: usize = 0;
    let mut v___x_3807_: usize = 0;
    let mut v_reuseFailAlloc_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3793_ = lean_usize_dec_eq(v_i_3790_, v_stop_3791_);
                if v___x_3793_ == 0 {
                    v_changesBefore_3794_ = lean_ctor_get(v_b_3792_, 0);
                    lean_inc(v_changesBefore_3794_);
                    v_changesAfter_3795_ = lean_ctor_get(v_b_3792_, 1);
                    lean_inc(v_changesAfter_3795_);
                    lean_dec_ref(v_b_3792_);
                    v___x_3796_ = lean_array_uget(v_as_3789_, v_i_3790_);
                    v_changesBefore_3797_ = lean_ctor_get(v___x_3796_, 0);
                    v_changesAfter_3798_ = lean_ctor_get(v___x_3796_, 1);
                    v_isSharedCheck_3810_ = (!lean_is_exclusive(v___x_3796_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v___x_3800_ = v___x_3796_;
                        v_isShared_3801_ = v_isSharedCheck_3810_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_changesAfter_3798_);
                        lean_inc(v_changesBefore_3797_);
                        lean_dec(v___x_3796_);
                        v___x_3800_ = lean_box(0);
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
                    lean_ctor_set(v___x_3800_, 1, v___x_3803_);
                    lean_ctor_set(v___x_3800_, 0, v___x_3802_);
                    v___x_3805_ = v___x_3800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3802_);
                    lean_ctor_set(v_reuseFailAlloc_3809_, 1, v___x_3803_);
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
    mut v_as_3811_: *mut LeanObject,
    mut v_i_3812_: *mut LeanObject,
    mut v_stop_3813_: *mut LeanObject,
    mut v_b_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3815_: usize = 0;
    let mut v_stop_boxed_3816_: usize = 0;
    let mut v_res_3817_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3815_ = lean_unbox_usize(v_i_3812_);
    lean_dec(v_i_3812_);
    v_stop_boxed_3816_ = lean_unbox_usize(v_stop_3813_);
    lean_dec(v_stop_3813_);
    v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_as_3811_, v_i_boxed_3815_, v_stop_boxed_3816_, v_b_3814_);
    lean_dec_ref(v_as_3811_);
    return v_res_3817_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(
    mut v_x_3818_: *mut LeanObject,
    mut v_x_3819_: *mut LeanObject,
    mut v_x_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3818_) == 5 {
                    v_fn_3821_ = lean_ctor_get(v_x_3818_, 0);
                    lean_inc_ref(v_fn_3821_);
                    v_arg_3822_ = lean_ctor_get(v_x_3818_, 1);
                    lean_inc_ref(v_arg_3822_);
                    lean_dec_ref_known(v_x_3818_, 2);
                    v___x_3823_ = lean_array_set(v_x_3819_, v_x_3820_, v_arg_3822_);
                    v___x_3824_ = lean_unsigned_to_nat(1);
                    v___x_3825_ = lean_nat_sub(v_x_3820_, v___x_3824_);
                    lean_dec(v_x_3820_);
                    v_x_3818_ = v_fn_3821_;
                    v_x_3819_ = v___x_3823_;
                    v_x_3820_ = v___x_3825_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_3820_);
                    v___x_3827_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3827_, 0, v_x_3818_);
                    lean_ctor_set(v___x_3827_, 1, v_x_3819_);
                    return v___x_3827_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0()
-> *mut LeanObject {
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3828_ = lean_box(0);
    v_dummy_3829_ = l_Lean_Expr_sort___override(v___x_3828_);
    return v_dummy_3829_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(
    mut v_snd_3830_: *mut LeanObject,
    mut v_before_3831_: *mut LeanObject,
    mut v_after_3832_: *mut LeanObject,
    mut v_as_3833_: *mut LeanObject,
    mut v_i_3834_: *mut LeanObject,
    mut v_j_3835_: *mut LeanObject,
    mut v_bs_3836_: *mut LeanObject,
    mut v___y_3837_: *mut LeanObject,
    mut v___y_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3843_: u8 = 0;
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v_pos_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3869_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut v_reuseFailAlloc_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3875_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3842_ = lean_unsigned_to_nat(0);
                v_isZero_3843_ = lean_nat_dec_eq(v_i_3834_, v_zero_3842_);
                if v_isZero_3843_ == 1 {
                    lean_dec(v_j_3835_);
                    lean_dec(v_i_3834_);
                    v___x_3844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3844_, 0, v_bs_3836_);
                    return v___x_3844_;
                } else {
                    v___x_3845_ = lean_array_fget(v_as_3833_, v_j_3835_);
                    v_fst_3846_ = lean_ctor_get(v___x_3845_, 0);
                    v_snd_3847_ = lean_ctor_get(v___x_3845_, 1);
                    v_isSharedCheck_3875_ = (!lean_is_exclusive(v___x_3845_)) as u8;
                    if v_isSharedCheck_3875_ == 0 {
                        v___x_3849_ = v___x_3845_;
                        v_isShared_3850_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3847_);
                        lean_inc(v_fst_3846_);
                        lean_dec(v___x_3845_);
                        v___x_3849_ = lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_pos_3851_ = lean_ctor_get(v_before_3831_, 1);
                v_pos_3852_ = lean_ctor_get(v_after_3832_, 1);
                v___x_3853_ = lean_array_get_size(v_snd_3830_);
                v___x_3854_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_3853_, v_j_3835_, v_pos_3851_);
                if v_isShared_3850_ == 0 {
                    lean_ctor_set(v___x_3849_, 1, v___x_3854_);
                    v___x_3856_ = v___x_3849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_fst_3846_);
                    lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3854_);
                    v___x_3856_ = v_reuseFailAlloc_3874_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3857_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_3853_, v_j_3835_, v_pos_3852_);
                v___x_3858_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3858_, 0, v_snd_3847_);
                lean_ctor_set(v___x_3858_, 1, v___x_3857_);
                v___x_3859_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                    v___x_3856_,
                    v___x_3858_,
                    v___y_3837_,
                    v___y_3838_,
                    v___y_3839_,
                    v___y_3840_,
                );
                if lean_obj_tag(v___x_3859_) == 0 {
                    v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
                    lean_inc(v_a_3860_);
                    lean_dec_ref_known(v___x_3859_, 1);
                    v_one_3861_ = lean_unsigned_to_nat(1);
                    v_n_3862_ = lean_nat_sub(v_i_3834_, v_one_3861_);
                    lean_dec(v_i_3834_);
                    v___x_3863_ = lean_nat_add(v_j_3835_, v_one_3861_);
                    lean_dec(v_j_3835_);
                    v___x_3864_ = lean_array_push(v_bs_3836_, v_a_3860_);
                    v_i_3834_ = v_n_3862_;
                    v_j_3835_ = v___x_3863_;
                    v_bs_3836_ = v___x_3864_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_bs_3836_);
                    lean_dec(v_j_3835_);
                    lean_dec(v_i_3834_);
                    v_a_3866_ = lean_ctor_get(v___x_3859_, 0);
                    v_isSharedCheck_3873_ = (!lean_is_exclusive(v___x_3859_)) as u8;
                    if v_isSharedCheck_3873_ == 0 {
                        v___x_3868_ = v___x_3859_;
                        v_isShared_3869_ = v_isSharedCheck_3873_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3866_);
                        lean_dec(v___x_3859_);
                        v___x_3868_ = lean_box(0);
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
                    v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
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
-> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__0;
    v___x_3878_ = l_Lean_stringToMessageData(v___x_3877_);
    return v___x_3878_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed(
    mut v_body_3879_: *mut LeanObject,
    mut v_pos_3880_: *mut LeanObject,
    mut v_body_3881_: *mut LeanObject,
    mut v_pos_3882_: *mut LeanObject,
    mut v_x_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3889_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3887_);
    lean_dec_ref(v___y_3886_);
    lean_dec(v___y_3885_);
    lean_dec_ref(v___y_3884_);
    lean_dec_ref(v_x_3883_);
    lean_dec(v_pos_3882_);
    lean_dec_ref(v_body_3881_);
    lean_dec(v_pos_3880_);
    lean_dec_ref(v_body_3879_);
    return v_res_3889_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(
    mut v_before_3890_: *mut LeanObject,
    mut v_after_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: u8 = 0;
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v___y_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v___x_3935_: u8 = 0;
    let mut v_expr_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_u2080_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut v_a_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut v_binderName_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3977_: u8 = 0;
    let mut v_expr_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4001_: u8 = 0;
    let mut v___x_4002_: u8 = 0;
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4008_: u8 = 0;
    let mut v___f_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4011_: u8 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4028_: u8 = 0;
    let mut v___x_4029_: u8 = 0;
    let mut v_changesBefore_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4040_: u8 = 0;
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4049_: u8 = 0;
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_reuseFailAlloc_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_unused_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_unused_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_3936_ = lean_ctor_get(v_before_3890_, 0);
                v_pos_3937_ = lean_ctor_get(v_before_3890_, 1);
                if lean_obj_tag(v_expr_3936_) == 7 {
                    v_binderName_3974_ = lean_ctor_get(v_expr_3936_, 0);
                    v_binderType_3975_ = lean_ctor_get(v_expr_3936_, 1);
                    v_body_3976_ = lean_ctor_get(v_expr_3936_, 2);
                    v_binderInfo_3977_ = lean_ctor_get_uint8(
                        v_expr_3936_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v_expr_3978_ = lean_ctor_get(v_after_3891_, 0);
                    v_pos_3979_ = lean_ctor_get(v_after_3891_, 1);
                    if lean_obj_tag(v_expr_3978_) == 7 {
                        v_binderName_4005_ = lean_ctor_get(v_expr_3978_, 0);
                        v_binderType_4006_ = lean_ctor_get(v_expr_3978_, 1);
                        v_body_4007_ = lean_ctor_get(v_expr_3978_, 2);
                        v_binderInfo_4008_ = lean_ctor_get_uint8(
                            v_expr_3978_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_inc(v_pos_3979_);
                        lean_inc_ref(v_body_4007_);
                        lean_inc(v_pos_3937_);
                        lean_inc_ref(v_body_3976_);
                        v___f_4009_ = lean_alloc_closure(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                        lean_closure_set(v___f_4009_, 0, v_body_3976_);
                        lean_closure_set(v___f_4009_, 1, v_pos_3937_);
                        lean_closure_set(v___f_4009_, 2, v_body_4007_);
                        lean_closure_set(v___f_4009_, 3, v_pos_3979_);
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
                    lean_dec_ref(v_after_3891_);
                    lean_dec_ref(v_before_3890_);
                    v___x_4063_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                    v___x_4064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4064_, 0, v___x_4063_);
                    return v___x_4064_;
                }
            }
            1 => {
                v___x_3904_ = lean_unsigned_to_nat(0);
                v___x_3905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v___y_3901_, v_before_3890_, v___x_3904_, v_a_3903_);
                lean_dec(v___y_3901_);
                return v___x_3905_;
            }
            2 => {
                if v___y_3914_ == 0 {
                    lean_dec_ref(v___y_3909_);
                    v___x_3915_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_3910_,
                        v___y_3911_,
                        v___y_3907_,
                    );
                    lean_dec_ref(v___y_3910_);
                    if lean_obj_tag(v___x_3915_) == 0 {
                        lean_dec_ref_known(v___x_3915_, 1);
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
                        lean_dec(v___y_3912_);
                        lean_dec_ref(v_before_3890_);
                        v_a_3917_ = lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3924_ = (!lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3924_ == 0 {
                            v___x_3919_ = v___x_3915_;
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3917_);
                            lean_dec(v___x_3915_);
                            v___x_3919_ = lean_box(0);
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3912_);
                    lean_dec_ref(v___y_3910_);
                    lean_dec_ref(v_before_3890_);
                    return v___y_3909_;
                }
            }
            3 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
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
                    lean_dec_ref(v_a_3933_);
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
                if lean_obj_tag(v___x_3944_) == 0 {
                    v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
                    lean_inc(v_a_3945_);
                    lean_dec_ref_known(v___x_3944_, 1);
                    v___x_3946_ = l_List_lengthTR___redArg(v___y_3939_);
                    v___x_3947_ = lean_box(0);
                    v___x_3948_ = l_List_mapM_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__2(v___y_3939_, v___x_3947_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
                    if lean_obj_tag(v___x_3948_) == 0 {
                        v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
                        lean_inc(v_a_3949_);
                        lean_dec_ref_known(v___x_3948_, 1);
                        lean_inc_n(v___x_3946_, 2);
                        v_body_u2080_3950_ =
                            l_Lean_Expr_getForallBodyMaxDepth(v___x_3946_, v_expr_3936_);
                        v___x_3951_ = lean_array_mk(v_a_3949_);
                        v___x_3952_ = lean_expr_instantiate_rev(v_body_u2080_3950_, v___x_3951_);
                        lean_dec_ref(v___x_3951_);
                        lean_dec_ref(v_body_u2080_3950_);
                        lean_inc(v_pos_3937_);
                        v___x_3953_ =
                            l_Lean_SubExpr_Pos_pushNthBindingBody(v___x_3946_, v_pos_3937_);
                        v___x_3954_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3954_, 0, v___x_3952_);
                        lean_ctor_set(v___x_3954_, 1, v___x_3953_);
                        v___x_3955_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
                            v___x_3954_,
                            v_after_3891_,
                            v___y_3940_,
                            v___y_3941_,
                            v___y_3942_,
                            v___y_3943_,
                        );
                        if lean_obj_tag(v___x_3955_) == 0 {
                            lean_dec(v_a_3945_);
                            v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
                            lean_inc(v_a_3956_);
                            lean_dec_ref_known(v___x_3955_, 1);
                            v___y_3898_ = v___y_3943_;
                            v___y_3899_ = v___y_3940_;
                            v___y_3900_ = v___y_3941_;
                            v___y_3901_ = v___x_3946_;
                            v___y_3902_ = v___y_3942_;
                            v_a_3903_ = v_a_3956_;
                            state = 1;
                            continue;
                        } else {
                            v_a_3957_ = lean_ctor_get(v___x_3955_, 0);
                            lean_inc(v_a_3957_);
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
                        lean_dec_ref(v_after_3891_);
                        v_a_3958_ = lean_ctor_get(v___x_3948_, 0);
                        v_isSharedCheck_3965_ = (!lean_is_exclusive(v___x_3948_)) as u8;
                        if v_isSharedCheck_3965_ == 0 {
                            v___x_3960_ = v___x_3948_;
                            v_isShared_3961_ = v_isSharedCheck_3965_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3958_);
                            lean_dec(v___x_3948_);
                            v___x_3960_ = lean_box(0);
                            v_isShared_3961_ = v_isSharedCheck_3965_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3939_);
                    lean_dec_ref(v_after_3891_);
                    lean_dec_ref(v_before_3890_);
                    v_a_3966_ = lean_ctor_get(v___x_3944_, 0);
                    v_isSharedCheck_3973_ = (!lean_is_exclusive(v___x_3944_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3968_ = v___x_3944_;
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3966_);
                        lean_dec(v___x_3944_);
                        v___x_3968_ = lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_3973_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                lean_inc(v_a_3958_);
                if v_isShared_3961_ == 0 {
                    v___x_3963_ = v___x_3960_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
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
                    v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
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
                if lean_obj_tag(v___x_3987_) == 1 {
                    v_val_3988_ = lean_ctor_get(v___x_3987_, 0);
                    lean_inc(v_val_3988_);
                    lean_dec_ref_known(v___x_3987_, 1);
                    v___x_3989_ = l_List_lengthTR___redArg(v_val_3988_);
                    v___x_3990_ = lean_unsigned_to_nat(0);
                    v___x_3991_ = lean_nat_dec_eq(v___x_3989_, v___x_3990_);
                    lean_dec(v___x_3989_);
                    if v___x_3991_ == 0 {
                        v___y_3939_ = v_val_3988_;
                        v___y_3940_ = v___y_3981_;
                        v___y_3941_ = v___y_3982_;
                        v___y_3942_ = v___y_3983_;
                        v___y_3943_ = v___y_3984_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3992_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___closed__1);
                        v___x_3993_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_3992_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
                        if lean_obj_tag(v___x_3993_) == 0 {
                            lean_dec_ref_known(v___x_3993_, 1);
                            v___y_3939_ = v_val_3988_;
                            v___y_3940_ = v___y_3981_;
                            v___y_3941_ = v___y_3982_;
                            v___y_3942_ = v___y_3983_;
                            v___y_3943_ = v___y_3984_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_val_3988_);
                            lean_dec_ref(v_after_3891_);
                            lean_dec_ref(v_before_3890_);
                            v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
                            v_isSharedCheck_4001_ = (!lean_is_exclusive(v___x_3993_)) as u8;
                            if v_isSharedCheck_4001_ == 0 {
                                v___x_3996_ = v___x_3993_;
                                v_isShared_3997_ = v_isSharedCheck_4001_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3994_);
                                lean_dec(v___x_3993_);
                                v___x_3996_ = lean_box(0);
                                v_isShared_3997_ = v_isSharedCheck_4001_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_3987_);
                    v___x_4002_ = 0;
                    v___x_4003_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                        v_before_3890_,
                        v_after_3891_,
                        v___x_4002_,
                    );
                    v___x_4004_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4004_, 0, v___x_4003_);
                    return v___x_4004_;
                }
            }
            12 => {
                if v_isShared_3997_ == 0 {
                    v___x_3999_ = v___x_3996_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
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
                    lean_dec_ref(v___f_4009_);
                    v___y_3981_ = v_a_3892_;
                    v___y_3982_ = v_a_3893_;
                    v___y_3983_ = v_a_3894_;
                    v___y_3984_ = v_a_3895_;
                    state = 11;
                    continue;
                } else {
                    lean_inc_ref(v_binderType_4006_);
                    lean_inc(v_pos_3979_);
                    lean_inc_ref(v_binderType_3975_);
                    lean_inc(v_binderName_3974_);
                    lean_inc(v_pos_3937_);
                    v_isSharedCheck_4058_ = (!lean_is_exclusive(v_before_3890_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v_unused_4059_ = lean_ctor_get(v_before_3890_, 1);
                        lean_dec(v_unused_4059_);
                        v_unused_4060_ = lean_ctor_get(v_before_3890_, 0);
                        lean_dec(v_unused_4060_);
                        v___x_4013_ = v_before_3890_;
                        v_isShared_4014_ = v_isSharedCheck_4058_;
                        state = 15;
                        continue;
                    } else {
                        lean_dec(v_before_3890_);
                        v___x_4013_ = lean_box(0);
                        v_isShared_4014_ = v_isSharedCheck_4058_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                v_isSharedCheck_4055_ = (!lean_is_exclusive(v_after_3891_)) as u8;
                if v_isSharedCheck_4055_ == 0 {
                    v_unused_4056_ = lean_ctor_get(v_after_3891_, 1);
                    lean_dec(v_unused_4056_);
                    v_unused_4057_ = lean_ctor_get(v_after_3891_, 0);
                    lean_dec(v_unused_4057_);
                    v___x_4016_ = v_after_3891_;
                    v_isShared_4017_ = v_isSharedCheck_4055_;
                    state = 16;
                    continue;
                } else {
                    lean_dec(v_after_3891_);
                    v___x_4016_ = lean_box(0);
                    v_isShared_4017_ = v_isSharedCheck_4055_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4018_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_3937_);
                lean_inc_ref(v_binderType_3975_);
                if v_isShared_4017_ == 0 {
                    lean_ctor_set(v___x_4016_, 1, v___x_4018_);
                    lean_ctor_set(v___x_4016_, 0, v_binderType_3975_);
                    v___x_4020_ = v___x_4016_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_binderType_3975_);
                    lean_ctor_set(v_reuseFailAlloc_4054_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4054_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4021_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_3979_);
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 1, v___x_4021_);
                    lean_ctor_set(v___x_4013_, 0, v_binderType_4006_);
                    v___x_4023_ = v___x_4013_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_binderType_4006_);
                    lean_ctor_set(v_reuseFailAlloc_4053_, 1, v___x_4021_);
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
                if lean_obj_tag(v___x_4024_) == 0 {
                    v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
                    v_isSharedCheck_4052_ = (!lean_is_exclusive(v___x_4024_)) as u8;
                    if v_isSharedCheck_4052_ == 0 {
                        v___x_4027_ = v___x_4024_;
                        v_isShared_4028_ = v_isSharedCheck_4052_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4025_);
                        lean_dec(v___x_4024_);
                        v___x_4027_ = lean_box(0);
                        v_isShared_4028_ = v_isSharedCheck_4052_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_4009_);
                    lean_dec(v_pos_3979_);
                    lean_dec_ref(v_binderType_3975_);
                    lean_dec(v_binderName_3974_);
                    lean_dec(v_pos_3937_);
                    return v___x_4024_;
                }
            }
            19 => {
                v___x_4029_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_4025_);
                if v___x_4029_ == 0 {
                    lean_dec_ref(v___f_4009_);
                    lean_dec_ref(v_binderType_3975_);
                    lean_dec(v_binderName_3974_);
                    v_changesBefore_4030_ = lean_ctor_get(v_a_4025_, 0);
                    lean_inc(v_changesBefore_4030_);
                    v_changesAfter_4031_ = lean_ctor_get(v_a_4025_, 1);
                    lean_inc(v_changesAfter_4031_);
                    lean_dec(v_a_4025_);
                    v___x_4032_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_3937_);
                    lean_dec(v_pos_3937_);
                    v___x_4033_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_3979_);
                    lean_dec(v_pos_3979_);
                    v___x_4034_ = 0;
                    v___x_4035_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
                            v___x_4032_,
                            v___x_4033_,
                            v___x_4034_,
                        );
                    v_changesBefore_4036_ = lean_ctor_get(v___x_4035_, 0);
                    v_changesAfter_4037_ = lean_ctor_get(v___x_4035_, 1);
                    v_isSharedCheck_4049_ = (!lean_is_exclusive(v___x_4035_)) as u8;
                    if v_isSharedCheck_4049_ == 0 {
                        v___x_4039_ = v___x_4035_;
                        v_isShared_4040_ = v_isSharedCheck_4049_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_changesAfter_4037_);
                        lean_inc(v_changesBefore_4036_);
                        lean_dec(v___x_4035_);
                        v___x_4039_ = lean_box(0);
                        v_isShared_4040_ = v_isSharedCheck_4049_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4027_);
                    lean_dec(v_a_4025_);
                    lean_dec(v_pos_3979_);
                    lean_dec(v_pos_3937_);
                    v___x_4050_ = 0;
                    v___x_4051_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__6___redArg(v_binderName_3974_, v_binderInfo_3977_, v_binderType_3975_, v___f_4009_, v___x_4050_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
                    return v___x_4051_;
                }
            }
            20 => {
                v___x_4041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesBefore_4030_, v_changesBefore_4036_);
                v___x_4042_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_changesAfter_4031_, v_changesAfter_4037_);
                if v_isShared_4040_ == 0 {
                    lean_ctor_set(v___x_4039_, 1, v___x_4042_);
                    lean_ctor_set(v___x_4039_, 0, v___x_4041_);
                    v___x_4044_ = v___x_4039_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4041_);
                    lean_ctor_set(v_reuseFailAlloc_4048_, 1, v___x_4042_);
                    v___x_4044_ = v_reuseFailAlloc_4048_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4028_ == 0 {
                    lean_ctor_set(v___x_4027_, 0, v___x_4044_);
                    v___x_4046_ = v___x_4027_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4044_);
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
    mut v_before_4065_: *mut LeanObject,
    mut v_after_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_u2081_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4103_: u8 = 0;
    let mut v_expr_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut v_unused_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: u8 = 0;
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u8 = 0;
    let mut v_args_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4139_: u8 = 0;
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: u8 = 0;
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: usize = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: usize = 0;
    let mut v___x_4157_: usize = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut v_a_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4170_: u8 = 0;
    let mut v_expr_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4177_: u8 = 0;
    let mut v_binderName_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4181_: u8 = 0;
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: u8 = 0;
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4201_: u8 = 0;
    let mut v_changesBefore_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: u8 = 0;
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesBefore_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_changesAfter_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut v_reuseFailAlloc_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v_unused_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: u8 = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4247_: u8 = 0;
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_unused_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut v_unused_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_4088_ = lean_ctor_get(v_before_4065_, 0);
                v_pos_4089_ = lean_ctor_get(v_before_4065_, 1);
                v_expr_4090_ = lean_ctor_get(v_after_4066_, 0);
                v_pos_4091_ = lean_ctor_get(v_after_4066_, 1);
                v___x_4100_ = lean_expr_eqv(v_expr_4088_, v_expr_4090_);
                if v___x_4100_ == 0 {
                    match lean_obj_tag(v_expr_4088_) {
                        10 => {
                            lean_inc_ref(v_expr_4088_);
                            lean_inc(v_pos_4089_);
                            v_isSharedCheck_4109_ = (!lean_is_exclusive(v_before_4065_)) as u8;
                            if v_isSharedCheck_4109_ == 0 {
                                v_unused_4110_ = lean_ctor_get(v_before_4065_, 1);
                                lean_dec(v_unused_4110_);
                                v_unused_4111_ = lean_ctor_get(v_before_4065_, 0);
                                lean_dec(v_unused_4111_);
                                v___x_4102_ = v_before_4065_;
                                v_isShared_4103_ = v_isSharedCheck_4109_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v_before_4065_);
                                v___x_4102_ = lean_box(0);
                                v_isShared_4103_ = v_isSharedCheck_4109_;
                                state = 6;
                                continue;
                            }
                        }
                        5 => match lean_obj_tag(v_expr_4090_) {
                            10 => {
                                lean_inc_ref(v_expr_4090_);
                                lean_inc(v_pos_4091_);
                                lean_dec_ref(v_after_4066_);
                                v_expr_4112_ = lean_ctor_get(v_expr_4090_, 1);
                                lean_inc_ref(v_expr_4112_);
                                lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4112_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            5 => {
                                v_dummy_4113_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___closed__0);
                                v_nargs_4114_ = l_Lean_Expr_getAppNumArgs(v_expr_4090_);
                                lean_inc(v_nargs_4114_);
                                v___x_4115_ = lean_mk_array(v_nargs_4114_, v_dummy_4113_);
                                v___x_4116_ = lean_unsigned_to_nat(1);
                                v___x_4117_ = lean_nat_sub(v_nargs_4114_, v___x_4116_);
                                lean_dec(v_nargs_4114_);
                                lean_inc_ref(v_expr_4090_);
                                v___x_4118_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_4090_, v___x_4115_, v___x_4117_);
                                v_fst_4119_ = lean_ctor_get(v___x_4118_, 0);
                                lean_inc(v_fst_4119_);
                                v_snd_4120_ = lean_ctor_get(v___x_4118_, 1);
                                lean_inc(v_snd_4120_);
                                lean_dec_ref(v___x_4118_);
                                v_nargs_4121_ = l_Lean_Expr_getAppNumArgs(v_expr_4088_);
                                lean_inc(v_nargs_4121_);
                                v___x_4122_ = lean_mk_array(v_nargs_4121_, v_dummy_4113_);
                                v___x_4123_ = lean_nat_sub(v_nargs_4121_, v___x_4116_);
                                lean_dec(v_nargs_4121_);
                                lean_inc_ref(v_expr_4088_);
                                v___x_4124_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__8(v_expr_4088_, v___x_4122_, v___x_4123_);
                                v_fst_4125_ = lean_ctor_get(v___x_4124_, 0);
                                lean_inc(v_fst_4125_);
                                v_snd_4126_ = lean_ctor_get(v___x_4124_, 1);
                                lean_inc(v_snd_4126_);
                                lean_dec_ref(v___x_4124_);
                                v___x_4127_ = lean_expr_eqv(v_fst_4119_, v_fst_4125_);
                                lean_dec(v_fst_4125_);
                                lean_dec(v_fst_4119_);
                                if v___x_4127_ == 0 {
                                    lean_dec(v_snd_4126_);
                                    lean_dec(v_snd_4120_);
                                    state = 3;
                                    continue;
                                } else {
                                    if v___x_4100_ == 0 {
                                        v___x_4128_ = lean_array_get_size(v_snd_4120_);
                                        v___x_4129_ = lean_array_get_size(v_snd_4126_);
                                        v___x_4130_ = lean_nat_dec_eq(v___x_4128_, v___x_4129_);
                                        if v___x_4130_ == 0 {
                                            lean_dec(v_snd_4126_);
                                            lean_dec(v_snd_4120_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v_args_4131_ =
                                                l_Array_zip___redArg(v_snd_4120_, v_snd_4126_);
                                            lean_dec(v_snd_4126_);
                                            v___x_4132_ = lean_array_get_size(v_args_4131_);
                                            v___x_4133_ = lean_unsigned_to_nat(0);
                                            v___x_4134_ =
                                                lean_mk_empty_array_with_capacity(v___x_4132_);
                                            v___x_4135_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4120_, v_before_4065_, v_after_4066_, v_args_4131_, v___x_4132_, v___x_4133_, v___x_4134_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                            lean_dec_ref(v_args_4131_);
                                            lean_dec_ref(v_after_4066_);
                                            lean_dec_ref(v_before_4065_);
                                            lean_dec(v_snd_4120_);
                                            if lean_obj_tag(v___x_4135_) == 0 {
                                                v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
                                                v_isSharedCheck_4162_ =
                                                    (!lean_is_exclusive(v___x_4135_)) as u8;
                                                if v_isSharedCheck_4162_ == 0 {
                                                    v___x_4138_ = v___x_4135_;
                                                    v_isShared_4139_ = v_isSharedCheck_4162_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4136_);
                                                    lean_dec(v___x_4135_);
                                                    v___x_4138_ = lean_box(0);
                                                    v_isShared_4139_ = v_isSharedCheck_4162_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                v_a_4163_ = lean_ctor_get(v___x_4135_, 0);
                                                v_isSharedCheck_4170_ =
                                                    (!lean_is_exclusive(v___x_4135_)) as u8;
                                                if v_isSharedCheck_4170_ == 0 {
                                                    v___x_4165_ = v___x_4135_;
                                                    v_isShared_4166_ = v_isSharedCheck_4170_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4163_);
                                                    lean_dec(v___x_4135_);
                                                    v___x_4165_ = lean_box(0);
                                                    v_isShared_4166_ = v_isSharedCheck_4170_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_snd_4126_);
                                        lean_dec(v_snd_4120_);
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
                            if lean_obj_tag(v_expr_4090_) == 10 {
                                lean_inc_ref(v_expr_4090_);
                                lean_inc(v_pos_4091_);
                                lean_dec_ref(v_after_4066_);
                                v_expr_4171_ = lean_ctor_get(v_expr_4090_, 1);
                                lean_inc_ref(v_expr_4171_);
                                lean_dec_ref_known(v_expr_4090_, 2);
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
                        6 => match lean_obj_tag(v_expr_4090_) {
                            10 => {
                                lean_inc_ref(v_expr_4090_);
                                lean_inc(v_pos_4091_);
                                lean_dec_ref(v_after_4066_);
                                v_expr_4173_ = lean_ctor_get(v_expr_4090_, 1);
                                lean_inc_ref(v_expr_4173_);
                                lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4173_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            6 => {
                                v_binderName_4174_ = lean_ctor_get(v_expr_4088_, 0);
                                v_binderType_4175_ = lean_ctor_get(v_expr_4088_, 1);
                                v_body_4176_ = lean_ctor_get(v_expr_4088_, 2);
                                v_binderInfo_4177_ = lean_ctor_get_uint8(
                                    v_expr_4088_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                );
                                v_binderName_4178_ = lean_ctor_get(v_expr_4090_, 0);
                                v_binderType_4179_ = lean_ctor_get(v_expr_4090_, 1);
                                v_body_4180_ = lean_ctor_get(v_expr_4090_, 2);
                                v_binderInfo_4181_ = lean_ctor_get_uint8(
                                    v_expr_4090_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
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
                                            lean_inc_ref(v_body_4180_);
                                            lean_inc_ref(v_binderType_4179_);
                                            lean_inc_ref(v_body_4176_);
                                            lean_inc_ref(v_binderType_4175_);
                                            lean_inc(v_pos_4091_);
                                            lean_inc(v_pos_4089_);
                                            v_isSharedCheck_4233_ =
                                                (!lean_is_exclusive(v_before_4065_)) as u8;
                                            if v_isSharedCheck_4233_ == 0 {
                                                v_unused_4234_ = lean_ctor_get(v_before_4065_, 1);
                                                lean_dec(v_unused_4234_);
                                                v_unused_4235_ = lean_ctor_get(v_before_4065_, 0);
                                                lean_dec(v_unused_4235_);
                                                v___x_4185_ = v_before_4065_;
                                                v_isShared_4186_ = v_isSharedCheck_4233_;
                                                state = 15;
                                                continue;
                                            } else {
                                                lean_dec(v_before_4065_);
                                                v___x_4185_ = lean_box(0);
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
                        11 => match lean_obj_tag(v_expr_4090_) {
                            10 => {
                                lean_inc_ref(v_expr_4090_);
                                lean_inc(v_pos_4091_);
                                lean_dec_ref(v_after_4066_);
                                v_expr_4236_ = lean_ctor_get(v_expr_4090_, 1);
                                lean_inc_ref(v_expr_4236_);
                                lean_dec_ref_known(v_expr_4090_, 2);
                                v_e_u2081_4093_ = v_expr_4236_;
                                v___y_4094_ = v_a_4067_;
                                v___y_4095_ = v_a_4068_;
                                v___y_4096_ = v_a_4069_;
                                v___y_4097_ = v_a_4070_;
                                state = 5;
                                continue;
                            }
                            11 => {
                                v_typeName_4237_ = lean_ctor_get(v_expr_4088_, 0);
                                v_idx_4238_ = lean_ctor_get(v_expr_4088_, 1);
                                v_struct_4239_ = lean_ctor_get(v_expr_4088_, 2);
                                v_typeName_4240_ = lean_ctor_get(v_expr_4090_, 0);
                                v_idx_4241_ = lean_ctor_get(v_expr_4090_, 1);
                                v_struct_4242_ = lean_ctor_get(v_expr_4090_, 2);
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
                                            lean_inc_ref(v_struct_4242_);
                                            lean_inc_ref(v_struct_4239_);
                                            lean_inc(v_pos_4091_);
                                            lean_inc(v_pos_4089_);
                                            v_isSharedCheck_4263_ =
                                                (!lean_is_exclusive(v_before_4065_)) as u8;
                                            if v_isSharedCheck_4263_ == 0 {
                                                v_unused_4264_ = lean_ctor_get(v_before_4065_, 1);
                                                lean_dec(v_unused_4264_);
                                                v_unused_4265_ = lean_ctor_get(v_before_4065_, 0);
                                                lean_dec(v_unused_4265_);
                                                v___x_4246_ = v_before_4065_;
                                                v_isShared_4247_ = v_isSharedCheck_4263_;
                                                state = 23;
                                                continue;
                                            } else {
                                                lean_dec(v_before_4065_);
                                                v___x_4246_ = lean_box(0);
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
                            if lean_obj_tag(v_expr_4090_) == 10 {
                                lean_inc_ref(v_expr_4090_);
                                lean_inc(v_pos_4091_);
                                lean_dec_ref(v_after_4066_);
                                v_expr_4266_ = lean_ctor_get(v_expr_4090_, 1);
                                lean_inc_ref(v_expr_4266_);
                                lean_dec_ref_known(v_expr_4090_, 2);
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
                    lean_dec_ref(v_after_4066_);
                    lean_dec_ref(v_before_4065_);
                    v___x_4267_ = l___private_Lean_Widget_Diff_0__Lean_Widget_instEmptyCollectionExprDiff___closed__0;
                    v___x_4268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4268_, 0, v___x_4267_);
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
                v___x_4075_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4075_, 0, v___x_4074_);
                return v___x_4075_;
            }
            2 => {
                v___x_4077_ = 0;
                v___x_4078_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4077_,
                );
                v___x_4079_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4079_, 0, v___x_4078_);
                return v___x_4079_;
            }
            3 => {
                v___x_4081_ = 0;
                v___x_4082_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4081_,
                );
                v___x_4083_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4083_, 0, v___x_4082_);
                return v___x_4083_;
            }
            4 => {
                v___x_4085_ = 0;
                v___x_4086_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChange(
                    v_before_4065_,
                    v_after_4066_,
                    v___x_4085_,
                );
                v___x_4087_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                return v___x_4087_;
            }
            5 => {
                v___x_4098_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4098_, 0, v_e_u2081_4093_);
                lean_ctor_set(v___x_4098_, 1, v_pos_4091_);
                v_after_4066_ = v___x_4098_;
                v_a_4067_ = v___y_4094_;
                v_a_4068_ = v___y_4095_;
                v_a_4069_ = v___y_4096_;
                v_a_4070_ = v___y_4097_;
                state = 0;
                continue;
            }
            6 => {
                v_expr_4104_ = lean_ctor_get(v_expr_4088_, 1);
                lean_inc_ref(v_expr_4104_);
                lean_dec_ref_known(v_expr_4088_, 2);
                if v_isShared_4103_ == 0 {
                    lean_ctor_set(v___x_4102_, 0, v_expr_4104_);
                    v___x_4106_ = v___x_4102_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_expr_4104_);
                    lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_pos_4089_);
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
                    lean_dec(v_a_4136_);
                    if v_isShared_4139_ == 0 {
                        lean_ctor_set(v___x_4138_, 0, v___x_4140_);
                        v___x_4144_ = v___x_4138_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4140_);
                        v___x_4144_ = v_reuseFailAlloc_4145_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_4146_ = lean_nat_dec_le(v___x_4141_, v___x_4141_);
                    if v___x_4146_ == 0 {
                        if v___x_4142_ == 0 {
                            lean_dec(v_a_4136_);
                            if v_isShared_4139_ == 0 {
                                lean_ctor_set(v___x_4138_, 0, v___x_4140_);
                                v___x_4148_ = v___x_4138_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4140_);
                                v___x_4148_ = v_reuseFailAlloc_4149_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___x_4150_ = 0usize;
                            v___x_4151_ = lean_usize_of_nat(v___x_4141_);
                            v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_4136_, v___x_4150_, v___x_4151_, v___x_4140_);
                            lean_dec(v_a_4136_);
                            if v_isShared_4139_ == 0 {
                                lean_ctor_set(v___x_4138_, 0, v___x_4152_);
                                v___x_4154_ = v___x_4138_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                                v___x_4154_ = v_reuseFailAlloc_4155_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_4156_ = 0usize;
                        v___x_4157_ = lean_usize_of_nat(v___x_4141_);
                        v___x_4158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__10(v_a_4136_, v___x_4156_, v___x_4157_, v___x_4140_);
                        lean_dec(v_a_4136_);
                        if v_isShared_4139_ == 0 {
                            lean_ctor_set(v___x_4138_, 0, v___x_4158_);
                            v___x_4160_ = v___x_4138_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
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
                    v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
                    v___x_4168_ = v_reuseFailAlloc_4169_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4168_;
            }
            15 => {
                v_isSharedCheck_4230_ = (!lean_is_exclusive(v_after_4066_)) as u8;
                if v_isSharedCheck_4230_ == 0 {
                    v_unused_4231_ = lean_ctor_get(v_after_4066_, 1);
                    lean_dec(v_unused_4231_);
                    v_unused_4232_ = lean_ctor_get(v_after_4066_, 0);
                    lean_dec(v_unused_4232_);
                    v___x_4188_ = v_after_4066_;
                    v_isShared_4189_ = v_isSharedCheck_4230_;
                    state = 16;
                    continue;
                } else {
                    lean_dec(v_after_4066_);
                    v___x_4188_ = lean_box(0);
                    v_isShared_4189_ = v_isSharedCheck_4230_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4190_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_4089_);
                if v_isShared_4189_ == 0 {
                    lean_ctor_set(v___x_4188_, 1, v___x_4190_);
                    lean_ctor_set(v___x_4188_, 0, v_binderType_4175_);
                    v___x_4192_ = v___x_4188_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_binderType_4175_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 1, v___x_4190_);
                    v___x_4192_ = v_reuseFailAlloc_4229_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4193_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_4091_);
                if v_isShared_4186_ == 0 {
                    lean_ctor_set(v___x_4185_, 1, v___x_4193_);
                    lean_ctor_set(v___x_4185_, 0, v_binderType_4179_);
                    v___x_4195_ = v___x_4185_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_binderType_4179_);
                    lean_ctor_set(v_reuseFailAlloc_4228_, 1, v___x_4193_);
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
                if lean_obj_tag(v___x_4196_) == 0 {
                    v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
                    v_isSharedCheck_4227_ = (!lean_is_exclusive(v___x_4196_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4199_ = v___x_4196_;
                        v_isShared_4200_ = v_isSharedCheck_4227_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_4197_);
                        lean_dec(v___x_4196_);
                        v___x_4199_ = lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4227_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_body_4180_);
                    lean_dec_ref(v_body_4176_);
                    lean_dec(v_pos_4091_);
                    lean_dec(v_pos_4089_);
                    return v___x_4196_;
                }
            }
            19 => {
                v___x_4201_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_isEmpty(v_a_4197_);
                if v___x_4201_ == 0 {
                    lean_dec_ref(v_body_4180_);
                    lean_dec_ref(v_body_4176_);
                    v_changesBefore_4202_ = lean_ctor_get(v_a_4197_, 0);
                    lean_inc(v_changesBefore_4202_);
                    v_changesAfter_4203_ = lean_ctor_get(v_a_4197_, 1);
                    lean_inc(v_changesAfter_4203_);
                    lean_dec(v_a_4197_);
                    v___x_4204_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4089_);
                    lean_dec(v_pos_4089_);
                    v___x_4205_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4091_);
                    lean_dec(v_pos_4091_);
                    v___x_4206_ = 0;
                    v___x_4207_ =
                        l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiff_withChangePos(
                            v___x_4204_,
                            v___x_4205_,
                            v___x_4206_,
                        );
                    v_changesBefore_4208_ = lean_ctor_get(v___x_4207_, 0);
                    v_changesAfter_4209_ = lean_ctor_get(v___x_4207_, 1);
                    v_isSharedCheck_4221_ = (!lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4211_ = v___x_4207_;
                        v_isShared_4212_ = v_isSharedCheck_4221_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_changesAfter_4209_);
                        lean_inc(v_changesBefore_4208_);
                        lean_dec(v___x_4207_);
                        v___x_4211_ = lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4221_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4199_);
                    lean_dec(v_a_4197_);
                    v___x_4222_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4089_);
                    lean_dec(v_pos_4089_);
                    v___x_4223_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4223_, 0, v_body_4176_);
                    lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                    v___x_4224_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4091_);
                    lean_dec(v_pos_4091_);
                    v___x_4225_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4225_, 0, v_body_4180_);
                    lean_ctor_set(v___x_4225_, 1, v___x_4224_);
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
                    lean_ctor_set(v___x_4211_, 1, v___x_4214_);
                    lean_ctor_set(v___x_4211_, 0, v___x_4213_);
                    v___x_4216_ = v___x_4211_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4213_);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4214_);
                    v___x_4216_ = v_reuseFailAlloc_4220_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_4200_ == 0 {
                    lean_ctor_set(v___x_4199_, 0, v___x_4216_);
                    v___x_4218_ = v___x_4199_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4218_;
            }
            23 => {
                v_isSharedCheck_4260_ = (!lean_is_exclusive(v_after_4066_)) as u8;
                if v_isSharedCheck_4260_ == 0 {
                    v_unused_4261_ = lean_ctor_get(v_after_4066_, 1);
                    lean_dec(v_unused_4261_);
                    v_unused_4262_ = lean_ctor_get(v_after_4066_, 0);
                    lean_dec(v_unused_4262_);
                    v___x_4249_ = v_after_4066_;
                    v_isShared_4250_ = v_isSharedCheck_4260_;
                    state = 24;
                    continue;
                } else {
                    lean_dec(v_after_4066_);
                    v___x_4249_ = lean_box(0);
                    v_isShared_4250_ = v_isSharedCheck_4260_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4251_ = l_Lean_SubExpr_Pos_pushProj(v_pos_4089_);
                lean_dec(v_pos_4089_);
                if v_isShared_4250_ == 0 {
                    lean_ctor_set(v___x_4249_, 1, v___x_4251_);
                    lean_ctor_set(v___x_4249_, 0, v_struct_4239_);
                    v___x_4253_ = v___x_4249_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_struct_4239_);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 1, v___x_4251_);
                    v___x_4253_ = v_reuseFailAlloc_4259_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4254_ = l_Lean_SubExpr_Pos_pushProj(v_pos_4091_);
                lean_dec(v_pos_4091_);
                if v_isShared_4247_ == 0 {
                    lean_ctor_set(v___x_4246_, 1, v___x_4254_);
                    lean_ctor_set(v___x_4246_, 0, v_struct_4242_);
                    v___x_4256_ = v___x_4246_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_struct_4242_);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 1, v___x_4254_);
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
    mut v_body_4269_: *mut LeanObject,
    mut v_pos_4270_: *mut LeanObject,
    mut v_body_4271_: *mut LeanObject,
    mut v_pos_4272_: *mut LeanObject,
    mut v_x_4273_: *mut LeanObject,
    mut v___y_4274_: *mut LeanObject,
    mut v___y_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4279_ = lean_expr_instantiate1(v_body_4269_, v_x_4273_);
    v___x_4280_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4270_);
    v___x_4281_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4281_, 0, v___x_4279_);
    lean_ctor_set(v___x_4281_, 1, v___x_4280_);
    v___x_4282_ = lean_expr_instantiate1(v_body_4271_, v_x_4273_);
    v___x_4283_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_4272_);
    v___x_4284_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4284_, 0, v___x_4282_);
    lean_ctor_set(v___x_4284_, 1, v___x_4283_);
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
    mut v_snd_4286_: *mut LeanObject,
    mut v_before_4287_: *mut LeanObject,
    mut v_after_4288_: *mut LeanObject,
    mut v_as_4289_: *mut LeanObject,
    mut v_i_4290_: *mut LeanObject,
    mut v_j_4291_: *mut LeanObject,
    mut v_bs_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4298_: *mut LeanObject = core::ptr::null_mut();
    v_res_4298_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4286_, v_before_4287_, v_after_4288_, v_as_4289_, v_i_4290_, v_j_4291_, v_bs_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
    lean_dec(v___y_4296_);
    lean_dec_ref(v___y_4295_);
    lean_dec(v___y_4294_);
    lean_dec_ref(v___y_4293_);
    lean_dec_ref(v_as_4289_);
    lean_dec_ref(v_after_4288_);
    lean_dec_ref(v_before_4287_);
    lean_dec_ref(v_snd_4286_);
    return v_res_4298_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff___boxed(
    mut v_before_4299_: *mut LeanObject,
    mut v_after_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
    mut v_a_4303_: *mut LeanObject,
    mut v_a_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4306_: *mut LeanObject = core::ptr::null_mut();
    v_res_4306_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff(
        v_before_4299_,
        v_after_4300_,
        v_a_4301_,
        v_a_4302_,
        v_a_4303_,
        v_a_4304_,
    );
    lean_dec(v_a_4304_);
    lean_dec_ref(v_a_4303_);
    lean_dec(v_a_4302_);
    lean_dec_ref(v_a_4301_);
    return v_res_4306_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore___boxed(
    mut v_before_4307_: *mut LeanObject,
    mut v_after_4308_: *mut LeanObject,
    mut v_a_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4314_: *mut LeanObject = core::ptr::null_mut();
    v_res_4314_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore(
        v_before_4307_,
        v_after_4308_,
        v_a_4309_,
        v_a_4310_,
        v_a_4311_,
        v_a_4312_,
    );
    lean_dec(v_a_4312_);
    lean_dec_ref(v_a_4311_);
    lean_dec(v_a_4310_);
    lean_dec_ref(v_a_4309_);
    return v_res_4314_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(
    mut v_upperBound_4315_: *mut LeanObject,
    mut v_before_4316_: *mut LeanObject,
    mut v_inst_4317_: *mut LeanObject,
    mut v_R_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
    mut v_b_4320_: *mut LeanObject,
    mut v_c_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    v___x_4327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___redArg(v_upperBound_4315_, v_before_4316_, v_a_4319_, v_b_4320_);
    return v___x_4327_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1___boxed(
    mut v_upperBound_4328_: *mut LeanObject,
    mut v_before_4329_: *mut LeanObject,
    mut v_inst_4330_: *mut LeanObject,
    mut v_R_4331_: *mut LeanObject,
    mut v_a_4332_: *mut LeanObject,
    mut v_b_4333_: *mut LeanObject,
    mut v_c_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4340_: *mut LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__1(v_upperBound_4328_, v_before_4329_, v_inst_4330_, v_R_4331_, v_a_4332_, v_b_4333_, v_c_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
    lean_dec(v___y_4338_);
    lean_dec_ref(v___y_4337_);
    lean_dec(v___y_4336_);
    lean_dec_ref(v___y_4335_);
    lean_dec(v_upperBound_4328_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(
    mut v_00_u03b1_4341_: *mut LeanObject,
    mut v_msg_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    v___x_4348_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v_msg_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
    return v___x_4348_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___boxed(
    mut v_00_u03b1_4349_: *mut LeanObject,
    mut v_msg_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4356_: *mut LeanObject = core::ptr::null_mut();
    v_res_4356_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3(v_00_u03b1_4349_, v_msg_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
    lean_dec(v___y_4354_);
    lean_dec_ref(v___y_4353_);
    lean_dec(v___y_4352_);
    lean_dec_ref(v___y_4351_);
    return v_res_4356_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(
    mut v_b_u2082_4357_: u8,
    mut v_k_4358_: *mut LeanObject,
    mut v_t_4359_: *mut LeanObject,
    mut v_hl_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    v___x_4361_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___redArg(v_b_u2082_4357_, v_k_4358_, v_t_4359_);
    return v___x_4361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4___boxed(
    mut v_b_u2082_4362_: *mut LeanObject,
    mut v_k_4363_: *mut LeanObject,
    mut v_t_4364_: *mut LeanObject,
    mut v_hl_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_u2082_boxed_4366_: u8 = 0;
    let mut v_res_4367_: *mut LeanObject = core::ptr::null_mut();
    v_b_u2082_boxed_4366_ = (lean_unbox(v_b_u2082_4362_) as u8);
    v_res_4367_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__4(v_b_u2082_boxed_4366_, v_k_4363_, v_t_4364_, v_hl_4365_);
    return v_res_4367_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5(
    mut v_init_4368_: *mut LeanObject,
    mut v_t_4369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4370_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__5_spec__7(v_init_4368_, v_t_4369_);
    return v___x_4370_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(
    mut v_snd_4371_: *mut LeanObject,
    mut v_before_4372_: *mut LeanObject,
    mut v_after_4373_: *mut LeanObject,
    mut v_as_4374_: *mut LeanObject,
    mut v_i_4375_: *mut LeanObject,
    mut v_j_4376_: *mut LeanObject,
    mut v_inv_4377_: *mut LeanObject,
    mut v_bs_4378_: *mut LeanObject,
    mut v___y_4379_: *mut LeanObject,
    mut v___y_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    v___x_4384_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___redArg(v_snd_4371_, v_before_4372_, v_after_4373_, v_as_4374_, v_i_4375_, v_j_4376_, v_bs_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
    return v___x_4384_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9___boxed(
    mut v_snd_4385_: *mut LeanObject,
    mut v_before_4386_: *mut LeanObject,
    mut v_after_4387_: *mut LeanObject,
    mut v_as_4388_: *mut LeanObject,
    mut v_i_4389_: *mut LeanObject,
    mut v_j_4390_: *mut LeanObject,
    mut v_inv_4391_: *mut LeanObject,
    mut v_bs_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4398_: *mut LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_spec__9(v_snd_4385_, v_before_4386_, v_after_4387_, v_as_4388_, v_i_4389_, v_j_4390_, v_inv_4391_, v_bs_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
    lean_dec(v___y_4396_);
    lean_dec_ref(v___y_4395_);
    lean_dec(v___y_4394_);
    lean_dec_ref(v___y_4393_);
    lean_dec_ref(v_as_4388_);
    lean_dec_ref(v_after_4387_);
    lean_dec_ref(v_before_4386_);
    lean_dec_ref(v_snd_4385_);
    return v_res_4398_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
    mut v_e_u2080_4399_: *mut LeanObject,
    mut v_e_u2081_4400_: *mut LeanObject,
    mut v_useAfter_4401_: u8,
    mut v_a_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
    mut v_a_4404_: *mut LeanObject,
    mut v_a_4405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_u2080_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_u2081_4409_: *mut LeanObject = core::ptr::null_mut();
    v___x_4407_ = l_Lean_SubExpr_Pos_root;
    v_s_u2080_4408_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_s_u2080_4408_, 0, v_e_u2080_4399_);
    lean_ctor_set(v_s_u2080_4408_, 1, v___x_4407_);
    v_s_u2081_4409_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_s_u2081_4409_, 0, v_e_u2081_4400_);
    lean_ctor_set(v_s_u2081_4409_, 1, v___x_4407_);
    if v_useAfter_4401_ == 0 {
        let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_u2080_4412_: *mut LeanObject,
    mut v_e_u2081_4413_: *mut LeanObject,
    mut v_useAfter_4414_: *mut LeanObject,
    mut v_a_4415_: *mut LeanObject,
    mut v_a_4416_: *mut LeanObject,
    mut v_a_4417_: *mut LeanObject,
    mut v_a_4418_: *mut LeanObject,
    mut v_a_4419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_4420_: u8 = 0;
    let mut v_res_4421_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4420_ = (lean_unbox(v_useAfter_4414_) as u8);
    v_res_4421_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
        v_e_u2080_4412_,
        v_e_u2081_4413_,
        v_useAfter_boxed_4420_,
        v_a_4415_,
        v_a_4416_,
        v_a_4417_,
        v_a_4418_,
    );
    lean_dec(v_a_4418_);
    lean_dec_ref(v_a_4417_);
    lean_dec(v_a_4416_);
    lean_dec_ref(v_a_4415_);
    return v_res_4421_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(
    mut v_useAfter_4422_: u8,
    mut v_info_4423_: *mut LeanObject,
    mut v_d_4424_: u8,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    v___x_4430_ = l___private_Lean_Widget_Diff_0__Lean_Widget_ExprDiffTag_toDiffTag(
        v_useAfter_4422_,
        v_d_4424_,
    );
    v___x_4431_ = l_Lean_Widget_SubexprInfo_withDiffTag(v___x_4430_, v_info_4423_);
    v___x_4432_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4432_, 0, v___x_4431_);
    return v___x_4432_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed(
    mut v_useAfter_4433_: *mut LeanObject,
    mut v_info_4434_: *mut LeanObject,
    mut v_d_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_4441_: u8 = 0;
    let mut v_d_boxed_4442_: u8 = 0;
    let mut v_res_4443_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4441_ = (lean_unbox(v_useAfter_4433_) as u8);
    v_d_boxed_4442_ = (lean_unbox(v_d_4435_) as u8);
    v_res_4443_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0(
        v_useAfter_boxed_4441_,
        v_info_4434_,
        v_d_boxed_4442_,
        v___y_4436_,
        v___y_4437_,
        v___y_4438_,
        v___y_4439_,
    );
    lean_dec(v___y_4439_);
    lean_dec_ref(v___y_4438_);
    lean_dec(v___y_4437_);
    lean_dec_ref(v___y_4436_);
    return v_res_4443_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(
    mut v_f_4444_: *mut LeanObject,
    mut v_x_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4459_: u8 = 0;
    let mut v_a_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v_sz_4464_: usize = 0;
    let mut v___x_4465_: usize = 0;
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_a_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v_a_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4498_: u8 = 0;
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_a_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4445_) {
                0 => {
                    lean_dec_ref(v_f_4444_);
                    v_a_4451_ = lean_ctor_get(v_x_4445_, 0);
                    v_isSharedCheck_4459_ = (!lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4459_ == 0 {
                        v___x_4453_ = v_x_4445_;
                        v_isShared_4454_ = v_isSharedCheck_4459_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4451_);
                        lean_dec(v_x_4445_);
                        v___x_4453_ = lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4459_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4460_ = lean_ctor_get(v_x_4445_, 0);
                    v_isSharedCheck_4486_ = (!lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4486_ == 0 {
                        v___x_4462_ = v_x_4445_;
                        v_isShared_4463_ = v_isSharedCheck_4486_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4460_);
                        lean_dec(v_x_4445_);
                        v___x_4462_ = lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4486_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4487_ = lean_ctor_get(v_x_4445_, 0);
                    v_a_4488_ = lean_ctor_get(v_x_4445_, 1);
                    v_isSharedCheck_4514_ = (!lean_is_exclusive(v_x_4445_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4490_ = v_x_4445_;
                        v_isShared_4491_ = v_isSharedCheck_4514_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4488_);
                        lean_inc(v_a_4487_);
                        lean_dec(v_x_4445_);
                        v___x_4490_ = lean_box(0);
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
                    v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4457_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4457_, 0, v___x_4456_);
                return v___x_4457_;
            }
            3 => {
                v_sz_4464_ = lean_array_size(v_a_4460_);
                v___x_4465_ = 0usize;
                v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4444_, v_sz_4464_, v___x_4465_, v_a_4460_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
                if lean_obj_tag(v___x_4466_) == 0 {
                    v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
                    v_isSharedCheck_4477_ = (!lean_is_exclusive(v___x_4466_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4469_ = v___x_4466_;
                        v_isShared_4470_ = v_isSharedCheck_4477_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4467_);
                        lean_dec(v___x_4466_);
                        v___x_4469_ = lean_box(0);
                        v_isShared_4470_ = v_isSharedCheck_4477_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4462_);
                    v_a_4478_ = lean_ctor_get(v___x_4466_, 0);
                    v_isSharedCheck_4485_ = (!lean_is_exclusive(v___x_4466_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4480_ = v___x_4466_;
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4478_);
                        lean_dec(v___x_4466_);
                        v___x_4480_ = lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4463_ == 0 {
                    lean_ctor_set(v___x_4462_, 0, v_a_4467_);
                    v___x_4472_ = v___x_4462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4470_ == 0 {
                    lean_ctor_set(v___x_4469_, 0, v___x_4472_);
                    v___x_4474_ = v___x_4469_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 0, v___x_4472_);
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
                    v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4483_;
            }
            9 => {
                lean_inc_ref(v_f_4444_);
                lean_inc(v___y_4449_);
                lean_inc_ref(v___y_4448_);
                lean_inc(v___y_4447_);
                lean_inc_ref(v___y_4446_);
                v___x_4492_ = lean_apply_6(
                    v_f_4444_,
                    v_a_4487_,
                    v___y_4446_,
                    v___y_4447_,
                    v___y_4448_,
                    v___y_4449_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4492_) == 0 {
                    v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
                    lean_inc(v_a_4493_);
                    lean_dec_ref_known(v___x_4492_, 1);
                    v___x_4494_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4444_, v_a_4488_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
                    if lean_obj_tag(v___x_4494_) == 0 {
                        v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
                        v_isSharedCheck_4505_ = (!lean_is_exclusive(v___x_4494_)) as u8;
                        if v_isSharedCheck_4505_ == 0 {
                            v___x_4497_ = v___x_4494_;
                            v_isShared_4498_ = v_isSharedCheck_4505_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4495_);
                            lean_dec(v___x_4494_);
                            v___x_4497_ = lean_box(0);
                            v_isShared_4498_ = v_isSharedCheck_4505_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4493_);
                        lean_del_object(v___x_4490_);
                        return v___x_4494_;
                    }
                } else {
                    lean_del_object(v___x_4490_);
                    lean_dec_ref(v_a_4488_);
                    lean_dec_ref(v_f_4444_);
                    v_a_4506_ = lean_ctor_get(v___x_4492_, 0);
                    v_isSharedCheck_4513_ = (!lean_is_exclusive(v___x_4492_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4508_ = v___x_4492_;
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4506_);
                        lean_dec(v___x_4492_);
                        v___x_4508_ = lean_box(0);
                        v_isShared_4509_ = v_isSharedCheck_4513_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4491_ == 0 {
                    lean_ctor_set(v___x_4490_, 1, v_a_4495_);
                    lean_ctor_set(v___x_4490_, 0, v_a_4493_);
                    v___x_4500_ = v___x_4490_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4504_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4493_);
                    lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_a_4495_);
                    v___x_4500_ = v_reuseFailAlloc_4504_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4498_ == 0 {
                    lean_ctor_set(v___x_4497_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4497_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4503_, 0, v___x_4500_);
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
                    v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
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
    mut v_f_4515_: *mut LeanObject,
    mut v_sz_4516_: usize,
    mut v_i_4517_: usize,
    mut v_bs_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: usize = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4538_: u8 = 0;
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4524_ = lean_usize_dec_lt(v_i_4517_, v_sz_4516_);
                if v___x_4524_ == 0 {
                    lean_dec_ref(v_f_4515_);
                    v___x_4525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4525_, 0, v_bs_4518_);
                    return v___x_4525_;
                } else {
                    v_v_4526_ = lean_array_uget_borrowed(v_bs_4518_, v_i_4517_);
                    lean_inc(v_v_4526_);
                    lean_inc_ref(v_f_4515_);
                    v___x_4527_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4515_, v_v_4526_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
                    if lean_obj_tag(v___x_4527_) == 0 {
                        v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
                        lean_inc(v_a_4528_);
                        lean_dec_ref_known(v___x_4527_, 1);
                        v___x_4529_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4530_ = lean_array_uset(v_bs_4518_, v_i_4517_, v___x_4529_);
                        v___x_4531_ = 1usize;
                        v___x_4532_ = lean_usize_add(v_i_4517_, v___x_4531_);
                        v___x_4533_ = lean_array_uset(v_bs_x27_4530_, v_i_4517_, v_a_4528_);
                        v_i_4517_ = v___x_4532_;
                        v_bs_4518_ = v___x_4533_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4518_);
                        lean_dec_ref(v_f_4515_);
                        v_a_4535_ = lean_ctor_get(v___x_4527_, 0);
                        v_isSharedCheck_4542_ = (!lean_is_exclusive(v___x_4527_)) as u8;
                        if v_isSharedCheck_4542_ == 0 {
                            v___x_4537_ = v___x_4527_;
                            v_isShared_4538_ = v_isSharedCheck_4542_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4535_);
                            lean_dec(v___x_4527_);
                            v___x_4537_ = lean_box(0);
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
                    v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4535_);
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
    mut v_f_4543_: *mut LeanObject,
    mut v_sz_4544_: *mut LeanObject,
    mut v_i_4545_: *mut LeanObject,
    mut v_bs_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4552_: usize = 0;
    let mut v_i_boxed_4553_: usize = 0;
    let mut v_res_4554_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4552_ = lean_unbox_usize(v_sz_4544_);
    lean_dec(v_sz_4544_);
    v_i_boxed_4553_ = lean_unbox_usize(v_i_4545_);
    lean_dec(v_i_4545_);
    v_res_4554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4543_, v_sz_boxed_4552_, v_i_boxed_4553_, v_bs_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
    lean_dec(v___y_4550_);
    lean_dec_ref(v___y_4549_);
    lean_dec(v___y_4548_);
    lean_dec_ref(v___y_4547_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg___boxed(
    mut v_f_4555_: *mut LeanObject,
    mut v_x_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4562_: *mut LeanObject = core::ptr::null_mut();
    v_res_4562_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4555_, v_x_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
    lean_dec(v___y_4560_);
    lean_dec_ref(v___y_4559_);
    lean_dec(v___y_4558_);
    lean_dec_ref(v___y_4557_);
    return v_res_4562_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(
    mut v_t_4563_: *mut LeanObject,
    mut v_k_4564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: u8 = 0;
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_4563_) == 0 {
                    v_k_4565_ = lean_ctor_get(v_t_4563_, 1);
                    v_v_4566_ = lean_ctor_get(v_t_4563_, 2);
                    v_l_4567_ = lean_ctor_get(v_t_4563_, 3);
                    v_r_4568_ = lean_ctor_get(v_t_4563_, 4);
                    v___x_4569_ = lean_nat_dec_lt(v_k_4564_, v_k_4565_);
                    if v___x_4569_ == 0 {
                        v___x_4570_ = lean_nat_dec_eq(v_k_4564_, v_k_4565_);
                        if v___x_4570_ == 0 {
                            v_t_4563_ = v_r_4568_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_4566_);
                            v___x_4572_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4572_, 0, v_v_4566_);
                            return v___x_4572_;
                        }
                    } else {
                        v_t_4563_ = v_l_4567_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_4574_ = lean_box(0);
                    return v___x_4574_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg___boxed(
    mut v_t_4575_: *mut LeanObject,
    mut v_k_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4577_: *mut LeanObject = core::ptr::null_mut();
    v_res_4577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_4575_, v_k_4576_);
    lean_dec(v_k_4576_);
    lean_dec(v_t_4575_);
    return v_res_4577_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(
    mut v_pm_4578_: *mut LeanObject,
    mut v_merger_4579_: *mut LeanObject,
    mut v_info_4580_: *mut LeanObject,
    mut v___y_4581_: *mut LeanObject,
    mut v___y_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subexprPos_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    v_subexprPos_4586_ = lean_ctor_get(v_info_4580_, 1);
    v___x_4587_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_pm_4578_, v_subexprPos_4586_);
    if lean_obj_tag(v___x_4587_) == 0 {
        let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_merger_4579_);
        v___x_4588_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4588_, 0, v_info_4580_);
        return v___x_4588_;
    } else {
        let mut v_val_4589_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
        v_val_4589_ = lean_ctor_get(v___x_4587_, 0);
        lean_inc(v_val_4589_);
        lean_dec_ref_known(v___x_4587_, 1);
        lean_inc(v___y_4584_);
        lean_inc_ref(v___y_4583_);
        lean_inc(v___y_4582_);
        lean_inc_ref(v___y_4581_);
        v___x_4590_ = lean_apply_7(
            v_merger_4579_,
            v_info_4580_,
            v_val_4589_,
            v___y_4581_,
            v___y_4582_,
            v___y_4583_,
            v___y_4584_,
            lean_box(0),
        );
        return v___x_4590_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed(
    mut v_pm_4591_: *mut LeanObject,
    mut v_merger_4592_: *mut LeanObject,
    mut v_info_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4599_: *mut LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0(v_pm_4591_, v_merger_4592_, v_info_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
    lean_dec(v___y_4597_);
    lean_dec_ref(v___y_4596_);
    lean_dec(v___y_4595_);
    lean_dec_ref(v___y_4594_);
    lean_dec(v_pm_4591_);
    return v_res_4599_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(
    mut v_merger_4600_: *mut LeanObject,
    mut v_pm_4601_: *mut LeanObject,
    mut v_tt_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_pm_4601_) == 0 {
        let mut v___f_4608_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
        v___f_4608_ = lean_alloc_closure(l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
        lean_closure_set(v___f_4608_, 0, v_pm_4601_);
        lean_closure_set(v___f_4608_, 1, v_merger_4600_);
        v___x_4609_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v___f_4608_, v_tt_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
        return v___x_4609_;
    } else {
        let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_merger_4600_);
        v___x_4610_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4610_, 0, v_tt_4602_);
        return v___x_4610_;
    }
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg___boxed(
    mut v_merger_4611_: *mut LeanObject,
    mut v_pm_4612_: *mut LeanObject,
    mut v_tt_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4619_: *mut LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_4611_, v_pm_4612_, v_tt_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
    lean_dec(v___y_4617_);
    lean_dec_ref(v___y_4616_);
    lean_dec(v___y_4615_);
    lean_dec_ref(v___y_4614_);
    return v_res_4619_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
    mut v_useAfter_4620_: u8,
    mut v_diff_4621_: *mut LeanObject,
    mut v_info_u2081_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
    mut v_a_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v_a_4626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4629_: *mut LeanObject = core::ptr::null_mut();
    v___x_4628_ = lean_box((v_useAfter_4620_) as usize);
    v___f_4629_ = lean_alloc_closure(
        l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___lam__0___boxed
            as *mut core::ffi::c_void,
        8,
        1,
    );
    lean_closure_set(v___f_4629_, 0, v___x_4628_);
    if v_useAfter_4620_ == 0 {
        let mut v_changesBefore_4630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
        v_changesBefore_4630_ = lean_ctor_get(v_diff_4621_, 0);
        lean_inc(v_changesBefore_4630_);
        lean_dec_ref(v_diff_4621_);
        v___x_4631_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_4629_, v_changesBefore_4630_, v_info_u2081_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
        return v___x_4631_;
    } else {
        let mut v_changesAfter_4632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
        v_changesAfter_4632_ = lean_ctor_get(v_diff_4621_, 1);
        lean_inc(v_changesAfter_4632_);
        lean_dec_ref(v_diff_4621_);
        v___x_4633_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v___f_4629_, v_changesAfter_4632_, v_info_u2081_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
        return v___x_4633_;
    }
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags___boxed(
    mut v_useAfter_4634_: *mut LeanObject,
    mut v_diff_4635_: *mut LeanObject,
    mut v_info_u2081_4636_: *mut LeanObject,
    mut v_a_4637_: *mut LeanObject,
    mut v_a_4638_: *mut LeanObject,
    mut v_a_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_4642_: u8 = 0;
    let mut v_res_4643_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4642_ = (lean_unbox(v_useAfter_4634_) as u8);
    v_res_4643_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
        v_useAfter_boxed_4642_,
        v_diff_4635_,
        v_info_u2081_4636_,
        v_a_4637_,
        v_a_4638_,
        v_a_4639_,
        v_a_4640_,
    );
    lean_dec(v_a_4640_);
    lean_dec_ref(v_a_4639_);
    lean_dec(v_a_4638_);
    lean_dec_ref(v_a_4637_);
    return v_res_4643_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(
    mut v_00_u03b1_4644_: *mut LeanObject,
    mut v_merger_4645_: *mut LeanObject,
    mut v_pm_4646_: *mut LeanObject,
    mut v_tt_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    v___x_4653_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___redArg(v_merger_4645_, v_pm_4646_, v_tt_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
    return v___x_4653_;
}
pub unsafe fn l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0___boxed(
    mut v_00_u03b1_4654_: *mut LeanObject,
    mut v_merger_4655_: *mut LeanObject,
    mut v_pm_4656_: *mut LeanObject,
    mut v_tt_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4663_: *mut LeanObject = core::ptr::null_mut();
    v_res_4663_ = l_Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0(v_00_u03b1_4654_, v_merger_4655_, v_pm_4656_, v_tt_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
    lean_dec(v___y_4661_);
    lean_dec_ref(v___y_4660_);
    lean_dec(v___y_4659_);
    lean_dec_ref(v___y_4658_);
    return v_res_4663_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(
    mut v_00_u03b4_4664_: *mut LeanObject,
    mut v_t_4665_: *mut LeanObject,
    mut v_k_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___redArg(v_t_4665_, v_k_4666_);
    return v___x_4667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0___boxed(
    mut v_00_u03b4_4668_: *mut LeanObject,
    mut v_t_4669_: *mut LeanObject,
    mut v_k_4670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4671_: *mut LeanObject = core::ptr::null_mut();
    v_res_4671_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__0(v_00_u03b4_4668_, v_t_4669_, v_k_4670_);
    lean_dec(v_k_4670_);
    lean_dec(v_t_4669_);
    return v_res_4671_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(
    mut v_00_u03b1_4672_: *mut LeanObject,
    mut v_00_u03b2_4673_: *mut LeanObject,
    mut v_f_4674_: *mut LeanObject,
    mut v_x_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
    mut v___y_4678_: *mut LeanObject,
    mut v___y_4679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    v___x_4681_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___redArg(v_f_4674_, v_x_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
    return v___x_4681_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1___boxed(
    mut v_00_u03b1_4682_: *mut LeanObject,
    mut v_00_u03b2_4683_: *mut LeanObject,
    mut v_f_4684_: *mut LeanObject,
    mut v_x_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1(v_00_u03b1_4682_, v_00_u03b2_4683_, v_f_4684_, v_x_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
    lean_dec(v___y_4689_);
    lean_dec_ref(v___y_4688_);
    lean_dec(v___y_4687_);
    lean_dec_ref(v___y_4686_);
    return v_res_4691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4692_: *mut LeanObject,
    mut v_00_u03b2_4693_: *mut LeanObject,
    mut v_f_4694_: *mut LeanObject,
    mut v_sz_4695_: usize,
    mut v_i_4696_: usize,
    mut v_bs_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
    mut v___y_4699_: *mut LeanObject,
    mut v___y_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___redArg(v_f_4694_, v_sz_4695_, v_i_4696_, v_bs_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
    return v___x_4703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4704_: *mut LeanObject,
    mut v_00_u03b2_4705_: *mut LeanObject,
    mut v_f_4706_: *mut LeanObject,
    mut v_sz_4707_: *mut LeanObject,
    mut v_i_4708_: *mut LeanObject,
    mut v_bs_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
    mut v___y_4714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4715_: usize = 0;
    let mut v_i_boxed_4716_: usize = 0;
    let mut v_res_4717_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4715_ = lean_unbox_usize(v_sz_4707_);
    lean_dec(v_sz_4707_);
    v_i_boxed_4716_ = lean_unbox_usize(v_i_4708_);
    lean_dec(v_i_4708_);
    v_res_4717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_CodeWithInfos_mergePosMap___at___00__private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags_spec__0_spec__1_spec__2(v_00_u03b1_4704_, v_00_u03b2_4705_, v_f_4706_, v_sz_boxed_4715_, v_i_boxed_4716_, v_bs_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
    lean_dec(v___y_4713_);
    lean_dec_ref(v___y_4712_);
    lean_dec(v___y_4711_);
    lean_dec_ref(v___y_4710_);
    return v_res_4717_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(
    mut v_e_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4735_: u8 = 0;
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4721_ = l_Lean_Expr_hasMVar(v_e_4718_);
                if v___x_4721_ == 0 {
                    v___x_4722_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4722_, 0, v_e_4718_);
                    return v___x_4722_;
                } else {
                    v___x_4723_ = lean_st_ref_get(v___y_4719_);
                    v_mctx_4724_ = lean_ctor_get(v___x_4723_, 0);
                    lean_inc_ref(v_mctx_4724_);
                    lean_dec(v___x_4723_);
                    v___x_4725_ = l_Lean_instantiateMVarsCore(v_mctx_4724_, v_e_4718_);
                    v_fst_4726_ = lean_ctor_get(v___x_4725_, 0);
                    lean_inc(v_fst_4726_);
                    v_snd_4727_ = lean_ctor_get(v___x_4725_, 1);
                    lean_inc(v_snd_4727_);
                    lean_dec_ref(v___x_4725_);
                    v___x_4728_ = lean_st_ref_take(v___y_4719_);
                    v_cache_4729_ = lean_ctor_get(v___x_4728_, 1);
                    v_zetaDeltaFVarIds_4730_ = lean_ctor_get(v___x_4728_, 2);
                    v_postponed_4731_ = lean_ctor_get(v___x_4728_, 3);
                    v_diag_4732_ = lean_ctor_get(v___x_4728_, 4);
                    v_isSharedCheck_4741_ = (!lean_is_exclusive(v___x_4728_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v_unused_4742_ = lean_ctor_get(v___x_4728_, 0);
                        lean_dec(v_unused_4742_);
                        v___x_4734_ = v___x_4728_;
                        v_isShared_4735_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4732_);
                        lean_inc(v_postponed_4731_);
                        lean_inc(v_zetaDeltaFVarIds_4730_);
                        lean_inc(v_cache_4729_);
                        lean_dec(v___x_4728_);
                        v___x_4734_ = lean_box(0);
                        v_isShared_4735_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4735_ == 0 {
                    lean_ctor_set(v___x_4734_, 0, v_snd_4727_);
                    v___x_4737_ = v___x_4734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_snd_4727_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_cache_4729_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 2, v_zetaDeltaFVarIds_4730_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 3, v_postponed_4731_);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 4, v_diag_4732_);
                    v___x_4737_ = v_reuseFailAlloc_4740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4738_ = lean_st_ref_set(v___y_4719_, v___x_4737_);
                v___x_4739_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4739_, 0, v_fst_4726_);
                return v___x_4739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg___boxed(
    mut v_e_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4746_: *mut LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_4743_, v___y_4744_);
    lean_dec(v___y_4744_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(
    mut v_e_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    v___x_4753_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_e_4747_, v___y_4749_);
    return v___x_4753_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___boxed(
    mut v_e_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4760_: *mut LeanObject = core::ptr::null_mut();
    v_res_4760_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0(v_e_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
    lean_dec(v___y_4758_);
    lean_dec_ref(v___y_4757_);
    lean_dec(v___y_4756_);
    lean_dec_ref(v___y_4755_);
    return v_res_4760_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1()
-> *mut LeanObject {
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    v___x_4762_ =
        l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__0;
    v___x_4763_ = l_Lean_stringToMessageData(v___x_4762_);
    return v___x_4763_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(
    mut v_useAfter_4764_: u8,
    mut v_t_u2080_4765_: *mut LeanObject,
    mut v_h_u2081_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_names_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___y_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_a_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_a_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4772_ = lean_ctor_get(v_h_u2081_4766_, 0);
                v_fvarIds_4773_ = lean_ctor_get(v_h_u2081_4766_, 1);
                v_type_4774_ = lean_ctor_get(v_h_u2081_4766_, 2);
                v_val_x3f_4775_ = lean_ctor_get(v_h_u2081_4766_, 3);
                v_isInstance_x3f_4776_ = lean_ctor_get(v_h_u2081_4766_, 4);
                v_isType_x3f_4777_ = lean_ctor_get(v_h_u2081_4766_, 5);
                v_isInserted_x3f_4778_ = lean_ctor_get(v_h_u2081_4766_, 6);
                v_isRemoved_x3f_4779_ = lean_ctor_get(v_h_u2081_4766_, 7);
                v_isSharedCheck_4834_ = (!lean_is_exclusive(v_h_u2081_4766_)) as u8;
                if v_isSharedCheck_4834_ == 0 {
                    v___x_4781_ = v_h_u2081_4766_;
                    v_isShared_4782_ = v_isSharedCheck_4834_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_isRemoved_x3f_4779_);
                    lean_inc(v_isInserted_x3f_4778_);
                    lean_inc(v_isType_x3f_4777_);
                    lean_inc(v_isInstance_x3f_4776_);
                    lean_inc(v_val_x3f_4775_);
                    lean_inc(v_type_4774_);
                    lean_inc(v_fvarIds_4773_);
                    lean_inc(v_names_4772_);
                    lean_dec(v_h_u2081_4766_);
                    v___x_4781_ = lean_box(0);
                    v_isShared_4782_ = v_isSharedCheck_4834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4824_ = lean_unsigned_to_nat(0);
                v___x_4825_ = lean_array_get_size(v_fvarIds_4773_);
                v___x_4826_ = lean_nat_dec_lt(v___x_4824_, v___x_4825_);
                if v___x_4826_ == 0 {
                    lean_del_object(v___x_4781_);
                    lean_dec(v_isRemoved_x3f_4779_);
                    lean_dec(v_isInserted_x3f_4778_);
                    lean_dec(v_isType_x3f_4777_);
                    lean_dec(v_isInstance_x3f_4776_);
                    lean_dec(v_val_x3f_4775_);
                    lean_dec_ref(v_type_4774_);
                    lean_dec_ref(v_fvarIds_4773_);
                    lean_dec_ref(v_names_4772_);
                    lean_dec_ref(v_t_u2080_4765_);
                    v___x_4827_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff___closed__1);
                    v___x_4828_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_4827_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                    return v___x_4828_;
                } else {
                    v___x_4829_ = lean_array_fget_borrowed(v_fvarIds_4773_, v___x_4824_);
                    lean_inc(v___x_4829_);
                    v___x_4830_ = l_Lean_Expr_fvar___override(v___x_4829_);
                    lean_inc(v_a_4770_);
                    lean_inc_ref(v_a_4769_);
                    lean_inc(v_a_4768_);
                    lean_inc_ref(v_a_4767_);
                    v___x_4831_ =
                        lean_infer_type(v___x_4830_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
                    if lean_obj_tag(v___x_4831_) == 0 {
                        v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
                        lean_inc(v_a_4832_);
                        lean_dec_ref_known(v___x_4831_, 1);
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
                if lean_obj_tag(v___y_4784_) == 0 {
                    v_a_4785_ = lean_ctor_get(v___y_4784_, 0);
                    lean_inc(v_a_4785_);
                    lean_dec_ref_known(v___y_4784_, 1);
                    v___x_4786_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
                        v_t_u2080_4765_,
                        v_a_4785_,
                        v_useAfter_4764_,
                        v_a_4767_,
                        v_a_4768_,
                        v_a_4769_,
                        v_a_4770_,
                    );
                    if lean_obj_tag(v___x_4786_) == 0 {
                        v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
                        lean_inc(v_a_4787_);
                        lean_dec_ref_known(v___x_4786_, 1);
                        v___x_4788_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
                            v_useAfter_4764_,
                            v_a_4787_,
                            v_type_4774_,
                            v_a_4767_,
                            v_a_4768_,
                            v_a_4769_,
                            v_a_4770_,
                        );
                        if lean_obj_tag(v___x_4788_) == 0 {
                            v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
                            v_isSharedCheck_4799_ = (!lean_is_exclusive(v___x_4788_)) as u8;
                            if v_isSharedCheck_4799_ == 0 {
                                v___x_4791_ = v___x_4788_;
                                v_isShared_4792_ = v_isSharedCheck_4799_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4789_);
                                lean_dec(v___x_4788_);
                                v___x_4791_ = lean_box(0);
                                v_isShared_4792_ = v_isSharedCheck_4799_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4781_);
                            lean_dec(v_isRemoved_x3f_4779_);
                            lean_dec(v_isInserted_x3f_4778_);
                            lean_dec(v_isType_x3f_4777_);
                            lean_dec(v_isInstance_x3f_4776_);
                            lean_dec(v_val_x3f_4775_);
                            lean_dec_ref(v_fvarIds_4773_);
                            lean_dec_ref(v_names_4772_);
                            v_a_4800_ = lean_ctor_get(v___x_4788_, 0);
                            v_isSharedCheck_4807_ = (!lean_is_exclusive(v___x_4788_)) as u8;
                            if v_isSharedCheck_4807_ == 0 {
                                v___x_4802_ = v___x_4788_;
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4800_);
                                lean_dec(v___x_4788_);
                                v___x_4802_ = lean_box(0);
                                v_isShared_4803_ = v_isSharedCheck_4807_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4781_);
                        lean_dec(v_isRemoved_x3f_4779_);
                        lean_dec(v_isInserted_x3f_4778_);
                        lean_dec(v_isType_x3f_4777_);
                        lean_dec(v_isInstance_x3f_4776_);
                        lean_dec(v_val_x3f_4775_);
                        lean_dec_ref(v_type_4774_);
                        lean_dec_ref(v_fvarIds_4773_);
                        lean_dec_ref(v_names_4772_);
                        v_a_4808_ = lean_ctor_get(v___x_4786_, 0);
                        v_isSharedCheck_4815_ = (!lean_is_exclusive(v___x_4786_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v___x_4810_ = v___x_4786_;
                            v_isShared_4811_ = v_isSharedCheck_4815_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_4808_);
                            lean_dec(v___x_4786_);
                            v___x_4810_ = lean_box(0);
                            v_isShared_4811_ = v_isSharedCheck_4815_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4781_);
                    lean_dec(v_isRemoved_x3f_4779_);
                    lean_dec(v_isInserted_x3f_4778_);
                    lean_dec(v_isType_x3f_4777_);
                    lean_dec(v_isInstance_x3f_4776_);
                    lean_dec(v_val_x3f_4775_);
                    lean_dec_ref(v_type_4774_);
                    lean_dec_ref(v_fvarIds_4773_);
                    lean_dec_ref(v_names_4772_);
                    lean_dec_ref(v_t_u2080_4765_);
                    v_a_4816_ = lean_ctor_get(v___y_4784_, 0);
                    v_isSharedCheck_4823_ = (!lean_is_exclusive(v___y_4784_)) as u8;
                    if v_isSharedCheck_4823_ == 0 {
                        v___x_4818_ = v___y_4784_;
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4816_);
                        lean_dec(v___y_4784_);
                        v___x_4818_ = lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4782_ == 0 {
                    lean_ctor_set(v___x_4781_, 2, v_a_4789_);
                    v___x_4794_ = v___x_4781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_names_4772_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_fvarIds_4773_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_a_4789_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 3, v_val_x3f_4775_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 4, v_isInstance_x3f_4776_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 5, v_isType_x3f_4777_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 6, v_isInserted_x3f_4778_);
                    lean_ctor_set(v_reuseFailAlloc_4798_, 7, v_isRemoved_x3f_4779_);
                    v___x_4794_ = v_reuseFailAlloc_4798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4792_ == 0 {
                    lean_ctor_set(v___x_4791_, 0, v___x_4794_);
                    v___x_4796_ = v___x_4791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
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
                    v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
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
                    v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
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
                    v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
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
    mut v_useAfter_4835_: *mut LeanObject,
    mut v_t_u2080_4836_: *mut LeanObject,
    mut v_h_u2081_4837_: *mut LeanObject,
    mut v_a_4838_: *mut LeanObject,
    mut v_a_4839_: *mut LeanObject,
    mut v_a_4840_: *mut LeanObject,
    mut v_a_4841_: *mut LeanObject,
    mut v_a_4842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_4843_: u8 = 0;
    let mut v_res_4844_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4843_ = (lean_unbox(v_useAfter_4835_) as u8);
    v_res_4844_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(
        v_useAfter_boxed_4843_,
        v_t_u2080_4836_,
        v_h_u2081_4837_,
        v_a_4838_,
        v_a_4839_,
        v_a_4840_,
        v_a_4841_,
    );
    lean_dec(v_a_4841_);
    lean_dec_ref(v_a_4840_);
    lean_dec(v_a_4839_);
    lean_dec_ref(v_a_4838_);
    return v_res_4844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(
    mut v_ctx_u2080_4848_: *mut LeanObject,
    mut v_useAfter_4849_: u8,
    mut v_h_u2081_4850_: *mut LeanObject,
    mut v___x_4851_: *mut LeanObject,
    mut v___x_4852_: *mut LeanObject,
    mut v_as_4853_: *mut LeanObject,
    mut v_sz_4854_: usize,
    mut v_i_4855_: usize,
    mut v_b_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4886_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut v_a_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4900_: u8 = 0;
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_a_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_type_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4921_: u8 = 0;
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut v_unused_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v_unused_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: usize = 0;
    let mut v___x_4960_: usize = 0;
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4862_ = lean_usize_dec_lt(v_i_4855_, v_sz_4854_);
                if v___x_4862_ == 0 {
                    lean_dec_ref(v___x_4852_);
                    lean_dec_ref(v___x_4851_);
                    lean_dec_ref(v_h_u2081_4850_);
                    v___x_4863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4863_, 0, v_b_4856_);
                    return v___x_4863_;
                } else {
                    lean_dec_ref(v_b_4856_);
                    v_a_4864_ = lean_array_uget(v_as_4853_, v_i_4855_);
                    v_fst_4865_ = lean_ctor_get(v_a_4864_, 0);
                    v_snd_4866_ = lean_ctor_get(v_a_4864_, 1);
                    v_isSharedCheck_4962_ = (!lean_is_exclusive(v_a_4864_)) as u8;
                    if v_isSharedCheck_4962_ == 0 {
                        v___x_4868_ = v_a_4864_;
                        v_isShared_4869_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4866_);
                        lean_inc(v_fst_4865_);
                        lean_dec(v_a_4864_);
                        v___x_4868_ = lean_box(0);
                        v_isShared_4869_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4870_ = lean_box(0);
                v___x_4871_ = l_Lean_LocalContext_contains(v_ctx_u2080_4848_, v_snd_4866_);
                lean_dec(v_snd_4866_);
                if v___x_4871_ == 0 {
                    v___x_4872_ = lean_box(0);
                    v___x_4873_ = l_Lean_Name_str___override(v___x_4872_, v_fst_4865_);
                    v___x_4874_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_ctx_u2080_4848_, v___x_4873_);
                    lean_dec(v___x_4873_);
                    if lean_obj_tag(v___x_4874_) == 1 {
                        lean_dec_ref(v___x_4852_);
                        lean_dec_ref(v___x_4851_);
                        v_val_4875_ = lean_ctor_get(v___x_4874_, 0);
                        v_isSharedCheck_4913_ = (!lean_is_exclusive(v___x_4874_)) as u8;
                        if v_isSharedCheck_4913_ == 0 {
                            v___x_4877_ = v___x_4874_;
                            v_isShared_4878_ = v_isSharedCheck_4913_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_4875_);
                            lean_dec(v___x_4874_);
                            v___x_4877_ = lean_box(0);
                            v_isShared_4878_ = v_isSharedCheck_4913_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4874_);
                        if v_useAfter_4849_ == 0 {
                            v_type_4914_ = lean_ctor_get(v_h_u2081_4850_, 2);
                            v_val_x3f_4915_ = lean_ctor_get(v_h_u2081_4850_, 3);
                            v_isInstance_x3f_4916_ = lean_ctor_get(v_h_u2081_4850_, 4);
                            v_isType_x3f_4917_ = lean_ctor_get(v_h_u2081_4850_, 5);
                            v_isInserted_x3f_4918_ = lean_ctor_get(v_h_u2081_4850_, 6);
                            v_isSharedCheck_4932_ = (!lean_is_exclusive(v_h_u2081_4850_)) as u8;
                            if v_isSharedCheck_4932_ == 0 {
                                v_unused_4933_ = lean_ctor_get(v_h_u2081_4850_, 7);
                                lean_dec(v_unused_4933_);
                                v_unused_4934_ = lean_ctor_get(v_h_u2081_4850_, 1);
                                lean_dec(v_unused_4934_);
                                v_unused_4935_ = lean_ctor_get(v_h_u2081_4850_, 0);
                                lean_dec(v_unused_4935_);
                                v___x_4920_ = v_h_u2081_4850_;
                                v_isShared_4921_ = v_isSharedCheck_4932_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_isInserted_x3f_4918_);
                                lean_inc(v_isType_x3f_4917_);
                                lean_inc(v_isInstance_x3f_4916_);
                                lean_inc(v_val_x3f_4915_);
                                lean_inc(v_type_4914_);
                                lean_dec(v_h_u2081_4850_);
                                v___x_4920_ = lean_box(0);
                                v_isShared_4921_ = v_isSharedCheck_4932_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v_type_4936_ = lean_ctor_get(v_h_u2081_4850_, 2);
                            v_val_x3f_4937_ = lean_ctor_get(v_h_u2081_4850_, 3);
                            v_isInstance_x3f_4938_ = lean_ctor_get(v_h_u2081_4850_, 4);
                            v_isType_x3f_4939_ = lean_ctor_get(v_h_u2081_4850_, 5);
                            v_isRemoved_x3f_4940_ = lean_ctor_get(v_h_u2081_4850_, 7);
                            v_isSharedCheck_4954_ = (!lean_is_exclusive(v_h_u2081_4850_)) as u8;
                            if v_isSharedCheck_4954_ == 0 {
                                v_unused_4955_ = lean_ctor_get(v_h_u2081_4850_, 6);
                                lean_dec(v_unused_4955_);
                                v_unused_4956_ = lean_ctor_get(v_h_u2081_4850_, 1);
                                lean_dec(v_unused_4956_);
                                v_unused_4957_ = lean_ctor_get(v_h_u2081_4850_, 0);
                                lean_dec(v_unused_4957_);
                                v___x_4942_ = v_h_u2081_4850_;
                                v_isShared_4943_ = v_isSharedCheck_4954_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_isRemoved_x3f_4940_);
                                lean_inc(v_isType_x3f_4939_);
                                lean_inc(v_isInstance_x3f_4938_);
                                lean_inc(v_val_x3f_4937_);
                                lean_inc(v_type_4936_);
                                lean_dec(v_h_u2081_4850_);
                                v___x_4942_ = lean_box(0);
                                v_isShared_4943_ = v_isSharedCheck_4954_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4868_);
                    lean_dec(v_fst_4865_);
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
                lean_dec(v_val_4875_);
                v___x_4880_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v___x_4879_, v___y_4858_);
                if lean_obj_tag(v___x_4880_) == 0 {
                    v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
                    lean_inc(v_a_4881_);
                    lean_dec_ref_known(v___x_4880_, 1);
                    v___x_4882_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff(v_useAfter_4849_, v_a_4881_, v_h_u2081_4850_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
                    if lean_obj_tag(v___x_4882_) == 0 {
                        v_a_4883_ = lean_ctor_get(v___x_4882_, 0);
                        v_isSharedCheck_4896_ = (!lean_is_exclusive(v___x_4882_)) as u8;
                        if v_isSharedCheck_4896_ == 0 {
                            v___x_4885_ = v___x_4882_;
                            v_isShared_4886_ = v_isSharedCheck_4896_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4883_);
                            lean_dec(v___x_4882_);
                            v___x_4885_ = lean_box(0);
                            v_isShared_4886_ = v_isSharedCheck_4896_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4877_);
                        lean_del_object(v___x_4868_);
                        v_a_4897_ = lean_ctor_get(v___x_4882_, 0);
                        v_isSharedCheck_4904_ = (!lean_is_exclusive(v___x_4882_)) as u8;
                        if v_isSharedCheck_4904_ == 0 {
                            v___x_4899_ = v___x_4882_;
                            v_isShared_4900_ = v_isSharedCheck_4904_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_4897_);
                            lean_dec(v___x_4882_);
                            v___x_4899_ = lean_box(0);
                            v_isShared_4900_ = v_isSharedCheck_4904_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4877_);
                    lean_del_object(v___x_4868_);
                    lean_dec_ref(v_h_u2081_4850_);
                    v_a_4905_ = lean_ctor_get(v___x_4880_, 0);
                    v_isSharedCheck_4912_ = (!lean_is_exclusive(v___x_4880_)) as u8;
                    if v_isSharedCheck_4912_ == 0 {
                        v___x_4907_ = v___x_4880_;
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4905_);
                        lean_dec(v___x_4880_);
                        v___x_4907_ = lean_box(0);
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4878_ == 0 {
                    lean_ctor_set(v___x_4877_, 0, v_a_4883_);
                    v___x_4888_ = v___x_4877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4883_);
                    v___x_4888_ = v_reuseFailAlloc_4895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    lean_ctor_set(v___x_4868_, 0, v___x_4888_);
                    v___x_4890_ = v___x_4868_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4888_);
                    lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4870_);
                    v___x_4890_ = v_reuseFailAlloc_4894_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4886_ == 0 {
                    lean_ctor_set(v___x_4885_, 0, v___x_4890_);
                    v___x_4892_ = v___x_4885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4893_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4893_, 0, v___x_4890_);
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
                    v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
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
                    v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4910_;
            }
            11 => {
                v___x_4922_ = lean_box((v___x_4862_) as usize);
                v___x_4923_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4923_, 0, v___x_4922_);
                if v_isShared_4921_ == 0 {
                    lean_ctor_set(v___x_4920_, 7, v___x_4923_);
                    lean_ctor_set(v___x_4920_, 1, v___x_4852_);
                    lean_ctor_set(v___x_4920_, 0, v___x_4851_);
                    v___x_4925_ = v___x_4920_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4931_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 0, v___x_4851_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 1, v___x_4852_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 2, v_type_4914_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 3, v_val_x3f_4915_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 4, v_isInstance_x3f_4916_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 5, v_isType_x3f_4917_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 6, v_isInserted_x3f_4918_);
                    lean_ctor_set(v_reuseFailAlloc_4931_, 7, v___x_4923_);
                    v___x_4925_ = v_reuseFailAlloc_4931_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4926_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4926_, 0, v___x_4925_);
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    lean_ctor_set(v___x_4868_, 0, v___x_4926_);
                    v___x_4928_ = v___x_4868_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4926_);
                    lean_ctor_set(v_reuseFailAlloc_4930_, 1, v___x_4870_);
                    v___x_4928_ = v_reuseFailAlloc_4930_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4929_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4929_, 0, v___x_4928_);
                return v___x_4929_;
            }
            14 => {
                v___x_4944_ = lean_box((v___x_4862_) as usize);
                v___x_4945_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4945_, 0, v___x_4944_);
                if v_isShared_4943_ == 0 {
                    lean_ctor_set(v___x_4942_, 6, v___x_4945_);
                    lean_ctor_set(v___x_4942_, 1, v___x_4852_);
                    lean_ctor_set(v___x_4942_, 0, v___x_4851_);
                    v___x_4947_ = v___x_4942_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4953_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 0, v___x_4851_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 1, v___x_4852_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 2, v_type_4936_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 3, v_val_x3f_4937_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 4, v_isInstance_x3f_4938_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 5, v_isType_x3f_4939_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 6, v___x_4945_);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 7, v_isRemoved_x3f_4940_);
                    v___x_4947_ = v_reuseFailAlloc_4953_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4948_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4948_, 0, v___x_4947_);
                if v_isShared_4869_ == 0 {
                    lean_ctor_set(v___x_4868_, 1, v___x_4870_);
                    lean_ctor_set(v___x_4868_, 0, v___x_4948_);
                    v___x_4950_ = v___x_4868_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4948_);
                    lean_ctor_set(v_reuseFailAlloc_4952_, 1, v___x_4870_);
                    v___x_4950_ = v_reuseFailAlloc_4952_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4951_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4951_, 0, v___x_4950_);
                return v___x_4951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___boxed(
    mut v_ctx_u2080_4963_: *mut LeanObject,
    mut v_useAfter_4964_: *mut LeanObject,
    mut v_h_u2081_4965_: *mut LeanObject,
    mut v___x_4966_: *mut LeanObject,
    mut v___x_4967_: *mut LeanObject,
    mut v_as_4968_: *mut LeanObject,
    mut v_sz_4969_: *mut LeanObject,
    mut v_i_4970_: *mut LeanObject,
    mut v_b_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_4977_: u8 = 0;
    let mut v_sz_boxed_4978_: usize = 0;
    let mut v_i_boxed_4979_: usize = 0;
    let mut v_res_4980_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_4977_ = (lean_unbox(v_useAfter_4964_) as u8);
    v_sz_boxed_4978_ = lean_unbox_usize(v_sz_4969_);
    lean_dec(v_sz_4969_);
    v_i_boxed_4979_ = lean_unbox_usize(v_i_4970_);
    lean_dec(v_i_4970_);
    v_res_4980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_4963_, v_useAfter_boxed_4977_, v_h_u2081_4965_, v___x_4966_, v___x_4967_, v_as_4968_, v_sz_boxed_4978_, v_i_boxed_4979_, v_b_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
    lean_dec(v___y_4975_);
    lean_dec_ref(v___y_4974_);
    lean_dec(v___y_4973_);
    lean_dec_ref(v___y_4972_);
    lean_dec_ref(v_as_4968_);
    lean_dec_ref(v_ctx_u2080_4963_);
    return v_res_4980_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
    mut v_useAfter_4981_: u8,
    mut v_ctx_u2080_4982_: *mut LeanObject,
    mut v_h_u2081_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
    mut v_a_4985_: *mut LeanObject,
    mut v_a_4986_: *mut LeanObject,
    mut v_a_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_names_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4993_: usize = 0;
    let mut v___x_4994_: usize = 0;
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4999_: u8 = 0;
    let mut v_fst_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_a_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4989_ = lean_ctor_get(v_h_u2081_4983_, 0);
                v_fvarIds_4990_ = lean_ctor_get(v_h_u2081_4983_, 1);
                v___x_4991_ = l_Array_zip___redArg(v_names_4989_, v_fvarIds_4990_);
                v___x_4992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0___closed__0;
                v_sz_4993_ = lean_array_size(v___x_4991_);
                v___x_4994_ = 0usize;
                lean_inc_ref(v_fvarIds_4990_);
                lean_inc_ref(v_names_4989_);
                lean_inc_ref(v_h_u2081_4983_);
                v___x_4995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_spec__0(v_ctx_u2080_4982_, v_useAfter_4981_, v_h_u2081_4983_, v_names_4989_, v_fvarIds_4990_, v___x_4991_, v_sz_4993_, v___x_4994_, v___x_4992_, v_a_4984_, v_a_4985_, v_a_4986_, v_a_4987_);
                lean_dec_ref(v___x_4991_);
                if lean_obj_tag(v___x_4995_) == 0 {
                    v_a_4996_ = lean_ctor_get(v___x_4995_, 0);
                    v_isSharedCheck_5008_ = (!lean_is_exclusive(v___x_4995_)) as u8;
                    if v_isSharedCheck_5008_ == 0 {
                        v___x_4998_ = v___x_4995_;
                        v_isShared_4999_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4996_);
                        lean_dec(v___x_4995_);
                        v___x_4998_ = lean_box(0);
                        v_isShared_4999_ = v_isSharedCheck_5008_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u2081_4983_);
                    v_a_5009_ = lean_ctor_get(v___x_4995_, 0);
                    v_isSharedCheck_5016_ = (!lean_is_exclusive(v___x_4995_)) as u8;
                    if v_isSharedCheck_5016_ == 0 {
                        v___x_5011_ = v___x_4995_;
                        v_isShared_5012_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5009_);
                        lean_dec(v___x_4995_);
                        v___x_5011_ = lean_box(0);
                        v_isShared_5012_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5000_ = lean_ctor_get(v_a_4996_, 0);
                lean_inc(v_fst_5000_);
                lean_dec(v_a_4996_);
                if lean_obj_tag(v_fst_5000_) == 0 {
                    if v_isShared_4999_ == 0 {
                        lean_ctor_set(v___x_4998_, 0, v_h_u2081_4983_);
                        v___x_5002_ = v___x_4998_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_h_u2081_4983_);
                        v___x_5002_ = v_reuseFailAlloc_5003_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u2081_4983_);
                    v_val_5004_ = lean_ctor_get(v_fst_5000_, 0);
                    lean_inc(v_val_5004_);
                    lean_dec_ref_known(v_fst_5000_, 1);
                    if v_isShared_4999_ == 0 {
                        lean_ctor_set(v___x_4998_, 0, v_val_5004_);
                        v___x_5006_ = v___x_4998_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_val_5004_);
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
                    v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
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
    mut v_useAfter_5017_: *mut LeanObject,
    mut v_ctx_u2080_5018_: *mut LeanObject,
    mut v_h_u2081_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
    mut v_a_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
    mut v_a_5023_: *mut LeanObject,
    mut v_a_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_5025_: u8 = 0;
    let mut v_res_5026_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5025_ = (lean_unbox(v_useAfter_5017_) as u8);
    v_res_5026_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
        v_useAfter_boxed_5025_,
        v_ctx_u2080_5018_,
        v_h_u2081_5019_,
        v_a_5020_,
        v_a_5021_,
        v_a_5022_,
        v_a_5023_,
    );
    lean_dec(v_a_5023_);
    lean_dec_ref(v_a_5022_);
    lean_dec(v_a_5021_);
    lean_dec_ref(v_a_5020_);
    lean_dec_ref(v_ctx_u2080_5018_);
    return v_res_5026_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(
    mut v_useAfter_5027_: u8,
    mut v_lctx_u2080_5028_: *mut LeanObject,
    mut v_sz_5029_: usize,
    mut v_i_5030_: usize,
    mut v_bs_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: usize = 0;
    let mut v___x_5045_: usize = 0;
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5037_ = lean_usize_dec_lt(v_i_5030_, v_sz_5029_);
                if v___x_5037_ == 0 {
                    v___x_5038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5038_, 0, v_bs_5031_);
                    return v___x_5038_;
                } else {
                    v_v_5039_ = lean_array_uget_borrowed(v_bs_5031_, v_i_5030_);
                    lean_inc(v_v_5039_);
                    v___x_5040_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle(
                        v_useAfter_5027_,
                        v_lctx_u2080_5028_,
                        v_v_5039_,
                        v___y_5032_,
                        v___y_5033_,
                        v___y_5034_,
                        v___y_5035_,
                    );
                    if lean_obj_tag(v___x_5040_) == 0 {
                        v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
                        lean_inc(v_a_5041_);
                        lean_dec_ref_known(v___x_5040_, 1);
                        v___x_5042_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5043_ = lean_array_uset(v_bs_5031_, v_i_5030_, v___x_5042_);
                        v___x_5044_ = 1usize;
                        v___x_5045_ = lean_usize_add(v_i_5030_, v___x_5044_);
                        v___x_5046_ = lean_array_uset(v_bs_x27_5043_, v_i_5030_, v_a_5041_);
                        v_i_5030_ = v___x_5045_;
                        v_bs_5031_ = v___x_5046_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5031_);
                        v_a_5048_ = lean_ctor_get(v___x_5040_, 0);
                        v_isSharedCheck_5055_ = (!lean_is_exclusive(v___x_5040_)) as u8;
                        if v_isSharedCheck_5055_ == 0 {
                            v___x_5050_ = v___x_5040_;
                            v_isShared_5051_ = v_isSharedCheck_5055_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5048_);
                            lean_dec(v___x_5040_);
                            v___x_5050_ = lean_box(0);
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
                    v_reuseFailAlloc_5054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
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
    mut v_useAfter_5056_: *mut LeanObject,
    mut v_lctx_u2080_5057_: *mut LeanObject,
    mut v_sz_5058_: *mut LeanObject,
    mut v_i_5059_: *mut LeanObject,
    mut v_bs_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
    mut v___y_5062_: *mut LeanObject,
    mut v___y_5063_: *mut LeanObject,
    mut v___y_5064_: *mut LeanObject,
    mut v___y_5065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_5066_: u8 = 0;
    let mut v_sz_boxed_5067_: usize = 0;
    let mut v_i_boxed_5068_: usize = 0;
    let mut v_res_5069_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5066_ = (lean_unbox(v_useAfter_5056_) as u8);
    v_sz_boxed_5067_ = lean_unbox_usize(v_sz_5058_);
    lean_dec(v_sz_5058_);
    v_i_boxed_5068_ = lean_unbox_usize(v_i_5059_);
    lean_dec(v_i_5059_);
    v_res_5069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_boxed_5066_, v_lctx_u2080_5057_, v_sz_boxed_5067_, v_i_boxed_5068_, v_bs_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
    lean_dec(v___y_5064_);
    lean_dec_ref(v___y_5063_);
    lean_dec(v___y_5062_);
    lean_dec_ref(v___y_5061_);
    lean_dec_ref(v_lctx_u2080_5057_);
    return v_res_5069_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(
    mut v_useAfter_5070_: u8,
    mut v_lctx_u2080_5071_: *mut LeanObject,
    mut v_hs_u2081_5072_: *mut LeanObject,
    mut v_a_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
    mut v_a_5075_: *mut LeanObject,
    mut v_a_5076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_5078_: usize = 0;
    let mut v___x_5079_: usize = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    v_sz_5078_ = lean_array_size(v_hs_u2081_5072_);
    v___x_5079_ = 0usize;
    v___x_5080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses_spec__0(v_useAfter_5070_, v_lctx_u2080_5071_, v_sz_5078_, v___x_5079_, v_hs_u2081_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_);
    return v___x_5080_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses___boxed(
    mut v_useAfter_5081_: *mut LeanObject,
    mut v_lctx_u2080_5082_: *mut LeanObject,
    mut v_hs_u2081_5083_: *mut LeanObject,
    mut v_a_5084_: *mut LeanObject,
    mut v_a_5085_: *mut LeanObject,
    mut v_a_5086_: *mut LeanObject,
    mut v_a_5087_: *mut LeanObject,
    mut v_a_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_5089_: u8 = 0;
    let mut v_res_5090_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5089_ = (lean_unbox(v_useAfter_5081_) as u8);
    v_res_5090_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffHypotheses(
        v_useAfter_boxed_5089_,
        v_lctx_u2080_5082_,
        v_hs_u2081_5083_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
        v_a_5087_,
    );
    lean_dec(v_a_5087_);
    lean_dec_ref(v_a_5086_);
    lean_dec(v_a_5085_);
    lean_dec_ref(v_a_5084_);
    lean_dec_ref(v_lctx_u2080_5082_);
    return v_res_5090_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2()
-> *mut LeanObject {
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    v___x_5095_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__1;
    v___x_5096_ = l_Lean_stringToMessageData(v___x_5095_);
    return v___x_5096_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4()
-> *mut LeanObject {
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    v___x_5098_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__3;
    v___x_5099_ = l_Lean_stringToMessageData(v___x_5098_);
    return v___x_5099_;
}
pub unsafe fn _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6()
-> *mut LeanObject {
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5101_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__5;
    v___x_5102_ = l_Lean_stringToMessageData(v___x_5101_);
    return v___x_5102_;
}
pub unsafe fn l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(
    mut v_useAfter_5103_: u8,
    mut v_g_u2080_5104_: *mut LeanObject,
    mut v_i_u2081_5105_: *mut LeanObject,
    mut v_a_5106_: *mut LeanObject,
    mut v_a_5107_: *mut LeanObject,
    mut v_a_5108_: *mut LeanObject,
    mut v_a_5109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v_userName_x3f_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v_hyps_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5137_: u8 = 0;
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_a_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_a_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v_a_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5209_: u8 = 0;
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5213_: u8 = 0;
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_unused_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5218_: u8 = 0;
    let mut v_unused_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5111_ = lean_st_ref_get(v_a_5107_);
                v_mctx_5112_ = lean_ctor_get(v___x_5111_, 0);
                lean_inc_ref(v_mctx_5112_);
                lean_dec(v___x_5111_);
                v___x_5113_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5112_, v_g_u2080_5104_);
                lean_dec_ref(v_mctx_5112_);
                if lean_obj_tag(v___x_5113_) == 1 {
                    v_val_5114_ = lean_ctor_get(v___x_5113_, 0);
                    lean_inc(v_val_5114_);
                    lean_dec_ref_known(v___x_5113_, 1);
                    v_options_5115_ = lean_ctor_get(v_a_5108_, 2);
                    v_lctx_5116_ = lean_ctor_get(v_val_5114_, 1);
                    lean_inc_ref(v_lctx_5116_);
                    lean_dec(v_val_5114_);
                    v___x_5117_ = lean_box(1);
                    lean_inc_ref(v_options_5115_);
                    v___x_5118_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5118_, 0, v_options_5115_);
                    lean_ctor_set(v___x_5118_, 1, v___x_5117_);
                    lean_ctor_set(v___x_5118_, 2, v___x_5117_);
                    v___x_5119_ = l_Lean_LocalContext_sanitizeNames(v_lctx_5116_, v___x_5118_);
                    v_toInteractiveGoalCore_5120_ = lean_ctor_get(v_i_u2081_5105_, 0);
                    lean_inc_ref(v_toInteractiveGoalCore_5120_);
                    v_fst_5121_ = lean_ctor_get(v___x_5119_, 0);
                    v_isSharedCheck_5218_ = (!lean_is_exclusive(v___x_5119_)) as u8;
                    if v_isSharedCheck_5218_ == 0 {
                        v_unused_5219_ = lean_ctor_get(v___x_5119_, 1);
                        lean_dec(v_unused_5219_);
                        v___x_5123_ = v___x_5119_;
                        v_isShared_5124_ = v_isSharedCheck_5218_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_5121_);
                        lean_dec(v___x_5119_);
                        v___x_5123_ = lean_box(0);
                        v_isShared_5124_ = v_isSharedCheck_5218_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5113_);
                    lean_dec_ref(v_i_u2081_5105_);
                    v___x_5220_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__4);
                    v___x_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5221_, 0, v_g_u2080_5104_);
                    v___x_5222_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5222_, 0, v___x_5220_);
                    lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                    v___x_5223_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__6);
                    v___x_5224_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5224_, 0, v___x_5222_);
                    lean_ctor_set(v___x_5224_, 1, v___x_5223_);
                    v___x_5225_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_5224_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
                    return v___x_5225_;
                }
            }
            1 => {
                v_userName_x3f_5125_ = lean_ctor_get(v_i_u2081_5105_, 1);
                v_goalPrefix_5126_ = lean_ctor_get(v_i_u2081_5105_, 2);
                v_mvarId_5127_ = lean_ctor_get(v_i_u2081_5105_, 3);
                v_isRemoved_x3f_5128_ = lean_ctor_get(v_i_u2081_5105_, 5);
                v_isSharedCheck_5215_ = (!lean_is_exclusive(v_i_u2081_5105_)) as u8;
                if v_isSharedCheck_5215_ == 0 {
                    v_unused_5216_ = lean_ctor_get(v_i_u2081_5105_, 4);
                    lean_dec(v_unused_5216_);
                    v_unused_5217_ = lean_ctor_get(v_i_u2081_5105_, 0);
                    lean_dec(v_unused_5217_);
                    v___x_5130_ = v_i_u2081_5105_;
                    v_isShared_5131_ = v_isSharedCheck_5215_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_isRemoved_x3f_5128_);
                    lean_inc(v_mvarId_5127_);
                    lean_inc(v_goalPrefix_5126_);
                    lean_inc(v_userName_x3f_5125_);
                    lean_dec(v_i_u2081_5105_);
                    v___x_5130_ = lean_box(0);
                    v_isShared_5131_ = v_isSharedCheck_5215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hyps_5132_ = lean_ctor_get(v_toInteractiveGoalCore_5120_, 0);
                v_type_5133_ = lean_ctor_get(v_toInteractiveGoalCore_5120_, 1);
                v_ctx_5134_ = lean_ctor_get(v_toInteractiveGoalCore_5120_, 2);
                v_isSharedCheck_5214_ = (!lean_is_exclusive(v_toInteractiveGoalCore_5120_)) as u8;
                if v_isSharedCheck_5214_ == 0 {
                    v___x_5136_ = v_toInteractiveGoalCore_5120_;
                    v_isShared_5137_ = v_isSharedCheck_5214_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_ctx_5134_);
                    lean_inc(v_type_5133_);
                    lean_inc(v_hyps_5132_);
                    lean_dec(v_toInteractiveGoalCore_5120_);
                    v___x_5136_ = lean_box(0);
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
                lean_dec(v_fst_5121_);
                if lean_obj_tag(v___x_5138_) == 0 {
                    v_a_5139_ = lean_ctor_get(v___x_5138_, 0);
                    lean_inc(v_a_5139_);
                    lean_dec_ref_known(v___x_5138_, 1);
                    v___x_5140_ = l_Lean_Expr_mvar___override(v_g_u2080_5104_);
                    lean_inc(v_a_5109_);
                    lean_inc_ref(v_a_5108_);
                    lean_inc(v_a_5107_);
                    lean_inc_ref(v_a_5106_);
                    v___x_5141_ =
                        lean_infer_type(v___x_5140_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_);
                    if lean_obj_tag(v___x_5141_) == 0 {
                        v_a_5142_ = lean_ctor_get(v___x_5141_, 0);
                        lean_inc(v_a_5142_);
                        lean_dec_ref_known(v___x_5141_, 1);
                        v___x_5143_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_a_5142_, v_a_5107_);
                        v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
                        v_isSharedCheck_5197_ = (!lean_is_exclusive(v___x_5143_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5146_ = v___x_5143_;
                            v_isShared_5147_ = v_isSharedCheck_5197_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5144_);
                            lean_dec(v___x_5143_);
                            v___x_5146_ = lean_box(0);
                            v_isShared_5147_ = v_isSharedCheck_5197_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5139_);
                        lean_del_object(v___x_5136_);
                        lean_dec_ref(v_ctx_5134_);
                        lean_dec_ref(v_type_5133_);
                        lean_del_object(v___x_5130_);
                        lean_dec(v_isRemoved_x3f_5128_);
                        lean_dec(v_mvarId_5127_);
                        lean_dec_ref(v_goalPrefix_5126_);
                        lean_dec(v_userName_x3f_5125_);
                        lean_del_object(v___x_5123_);
                        v_a_5198_ = lean_ctor_get(v___x_5141_, 0);
                        v_isSharedCheck_5205_ = (!lean_is_exclusive(v___x_5141_)) as u8;
                        if v_isSharedCheck_5205_ == 0 {
                            v___x_5200_ = v___x_5141_;
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5198_);
                            lean_dec(v___x_5141_);
                            v___x_5200_ = lean_box(0);
                            v_isShared_5201_ = v_isSharedCheck_5205_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5136_);
                    lean_dec_ref(v_ctx_5134_);
                    lean_dec_ref(v_type_5133_);
                    lean_del_object(v___x_5130_);
                    lean_dec(v_isRemoved_x3f_5128_);
                    lean_dec(v_mvarId_5127_);
                    lean_dec_ref(v_goalPrefix_5126_);
                    lean_dec(v_userName_x3f_5125_);
                    lean_del_object(v___x_5123_);
                    lean_dec(v_g_u2080_5104_);
                    v_a_5206_ = lean_ctor_get(v___x_5138_, 0);
                    v_isSharedCheck_5213_ = (!lean_is_exclusive(v___x_5138_)) as u8;
                    if v_isSharedCheck_5213_ == 0 {
                        v___x_5208_ = v___x_5138_;
                        v_isShared_5209_ = v_isSharedCheck_5213_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5206_);
                        lean_dec(v___x_5138_);
                        v___x_5208_ = lean_box(0);
                        v_isShared_5209_ = v_isSharedCheck_5213_;
                        state = 17;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5148_ = lean_st_ref_get(v_a_5107_);
                v_mctx_5149_ = lean_ctor_get(v___x_5148_, 0);
                lean_inc_ref(v_mctx_5149_);
                lean_dec(v___x_5148_);
                v___x_5150_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5149_, v_mvarId_5127_);
                lean_dec_ref(v_mctx_5149_);
                if lean_obj_tag(v___x_5150_) == 1 {
                    lean_del_object(v___x_5146_);
                    lean_del_object(v___x_5123_);
                    v_val_5151_ = lean_ctor_get(v___x_5150_, 0);
                    lean_inc(v_val_5151_);
                    lean_dec_ref_known(v___x_5150_, 1);
                    v_type_5152_ = lean_ctor_get(v_val_5151_, 2);
                    lean_inc_ref(v_type_5152_);
                    lean_dec(v_val_5151_);
                    v___x_5153_ = l_Lean_instantiateMVars___at___00__private_Lean_Widget_Diff_0__Lean_Widget_diffHypothesesBundle_withTypeDiff_spec__0___redArg(v_type_5152_, v_a_5107_);
                    v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
                    lean_inc(v_a_5154_);
                    lean_dec_ref(v___x_5153_);
                    v___x_5155_ = l___private_Lean_Widget_Diff_0__Lean_Widget_exprDiff(
                        v_a_5144_,
                        v_a_5154_,
                        v_useAfter_5103_,
                        v_a_5106_,
                        v_a_5107_,
                        v_a_5108_,
                        v_a_5109_,
                    );
                    if lean_obj_tag(v___x_5155_) == 0 {
                        v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
                        lean_inc(v_a_5156_);
                        lean_dec_ref_known(v___x_5155_, 1);
                        v___x_5157_ = l___private_Lean_Widget_Diff_0__Lean_Widget_addDiffTags(
                            v_useAfter_5103_,
                            v_a_5156_,
                            v_type_5133_,
                            v_a_5106_,
                            v_a_5107_,
                            v_a_5108_,
                            v_a_5109_,
                        );
                        if lean_obj_tag(v___x_5157_) == 0 {
                            v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
                            v_isSharedCheck_5172_ = (!lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5172_ == 0 {
                                v___x_5160_ = v___x_5157_;
                                v_isShared_5161_ = v_isSharedCheck_5172_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5158_);
                                lean_dec(v___x_5157_);
                                v___x_5160_ = lean_box(0);
                                v_isShared_5161_ = v_isSharedCheck_5172_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5139_);
                            lean_del_object(v___x_5136_);
                            lean_dec_ref(v_ctx_5134_);
                            lean_del_object(v___x_5130_);
                            lean_dec(v_isRemoved_x3f_5128_);
                            lean_dec(v_mvarId_5127_);
                            lean_dec_ref(v_goalPrefix_5126_);
                            lean_dec(v_userName_x3f_5125_);
                            v_a_5173_ = lean_ctor_get(v___x_5157_, 0);
                            v_isSharedCheck_5180_ = (!lean_is_exclusive(v___x_5157_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5175_ = v___x_5157_;
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_5173_);
                                lean_dec(v___x_5157_);
                                v___x_5175_ = lean_box(0);
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5139_);
                        lean_del_object(v___x_5136_);
                        lean_dec_ref(v_ctx_5134_);
                        lean_dec_ref(v_type_5133_);
                        lean_del_object(v___x_5130_);
                        lean_dec(v_isRemoved_x3f_5128_);
                        lean_dec(v_mvarId_5127_);
                        lean_dec_ref(v_goalPrefix_5126_);
                        lean_dec(v_userName_x3f_5125_);
                        v_a_5181_ = lean_ctor_get(v___x_5155_, 0);
                        v_isSharedCheck_5188_ = (!lean_is_exclusive(v___x_5155_)) as u8;
                        if v_isSharedCheck_5188_ == 0 {
                            v___x_5183_ = v___x_5155_;
                            v_isShared_5184_ = v_isSharedCheck_5188_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5181_);
                            lean_dec(v___x_5155_);
                            v___x_5183_ = lean_box(0);
                            v_isShared_5184_ = v_isSharedCheck_5188_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5150_);
                    lean_dec(v_a_5144_);
                    lean_dec(v_a_5139_);
                    lean_del_object(v___x_5136_);
                    lean_dec_ref(v_ctx_5134_);
                    lean_dec_ref(v_type_5133_);
                    lean_del_object(v___x_5130_);
                    lean_dec(v_isRemoved_x3f_5128_);
                    lean_dec_ref(v_goalPrefix_5126_);
                    lean_dec(v_userName_x3f_5125_);
                    v___x_5189_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2_once), _init_l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__2);
                    if v_isShared_5147_ == 0 {
                        lean_ctor_set_tag(v___x_5146_, 1);
                        lean_ctor_set(v___x_5146_, 0, v_mvarId_5127_);
                        v___x_5191_ = v___x_5146_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5196_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_mvarId_5127_);
                        v___x_5191_ = v_reuseFailAlloc_5196_;
                        state = 13;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5137_ == 0 {
                    lean_ctor_set(v___x_5136_, 1, v_a_5158_);
                    lean_ctor_set(v___x_5136_, 0, v_a_5139_);
                    v___x_5163_ = v___x_5136_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5139_);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 1, v_a_5158_);
                    lean_ctor_set(v_reuseFailAlloc_5171_, 2, v_ctx_5134_);
                    v___x_5163_ = v_reuseFailAlloc_5171_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5164_ =
                    l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal___closed__0;
                if v_isShared_5131_ == 0 {
                    lean_ctor_set(v___x_5130_, 4, v___x_5164_);
                    lean_ctor_set(v___x_5130_, 0, v___x_5163_);
                    v___x_5166_ = v___x_5130_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v___x_5163_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_userName_x3f_5125_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 2, v_goalPrefix_5126_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 3, v_mvarId_5127_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 4, v___x_5164_);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 5, v_isRemoved_x3f_5128_);
                    v___x_5166_ = v_reuseFailAlloc_5170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5161_ == 0 {
                    lean_ctor_set(v___x_5160_, 0, v___x_5166_);
                    v___x_5168_ = v___x_5160_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5169_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5169_, 0, v___x_5166_);
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
                    v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
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
                    v_reuseFailAlloc_5187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
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
                    lean_ctor_set_tag(v___x_5123_, 7);
                    lean_ctor_set(v___x_5123_, 1, v___x_5191_);
                    lean_ctor_set(v___x_5123_, 0, v___x_5189_);
                    v___x_5193_ = v___x_5123_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5195_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5195_, 0, v___x_5189_);
                    lean_ctor_set(v_reuseFailAlloc_5195_, 1, v___x_5191_);
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
                    v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
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
                    v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
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
    mut v_useAfter_5226_: *mut LeanObject,
    mut v_g_u2080_5227_: *mut LeanObject,
    mut v_i_u2081_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
    mut v_a_5230_: *mut LeanObject,
    mut v_a_5231_: *mut LeanObject,
    mut v_a_5232_: *mut LeanObject,
    mut v_a_5233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_5234_: u8 = 0;
    let mut v_res_5235_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5234_ = (lean_unbox(v_useAfter_5226_) as u8);
    v_res_5235_ = l___private_Lean_Widget_Diff_0__Lean_Widget_diffInteractiveGoal(
        v_useAfter_boxed_5234_,
        v_g_u2080_5227_,
        v_i_u2081_5228_,
        v_a_5229_,
        v_a_5230_,
        v_a_5231_,
        v_a_5232_,
    );
    lean_dec(v_a_5232_);
    lean_dec_ref(v_a_5231_);
    lean_dec(v_a_5230_);
    lean_dec_ref(v_a_5229_);
    return v_res_5235_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
    mut v_opts_5236_: *mut LeanObject,
    mut v_opt_5237_: *mut LeanObject,
) -> u8 {
    let mut v_name_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    v_name_5238_ = lean_ctor_get(v_opt_5237_, 0);
    v_defValue_5239_ = lean_ctor_get(v_opt_5237_, 1);
    v_map_5240_ = lean_ctor_get(v_opts_5236_, 0);
    v___x_5241_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5240_,
            v_name_5238_,
        );
    if lean_obj_tag(v___x_5241_) == 0 {
        let mut v___x_5242_: u8 = 0;
        v___x_5242_ = (lean_unbox(v_defValue_5239_) as u8);
        return v___x_5242_;
    } else {
        let mut v_val_5243_: *mut LeanObject = core::ptr::null_mut();
        v_val_5243_ = lean_ctor_get(v___x_5241_, 0);
        lean_inc(v_val_5243_);
        lean_dec_ref_known(v___x_5241_, 1);
        if lean_obj_tag(v_val_5243_) == 1 {
            let mut v_v_5244_: u8 = 0;
            v_v_5244_ = lean_ctor_get_uint8(v_val_5243_, 0 as u32);
            lean_dec_ref_known(v_val_5243_, 0);
            return v_v_5244_;
        } else {
            let mut v___x_5245_: u8 = 0;
            lean_dec(v_val_5243_);
            v___x_5245_ = (lean_unbox(v_defValue_5239_) as u8);
            return v___x_5245_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0___boxed(
    mut v_opts_5246_: *mut LeanObject,
    mut v_opt_5247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5248_: u8 = 0;
    let mut v_r_5249_: *mut LeanObject = core::ptr::null_mut();
    v_res_5248_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
        v_opts_5246_,
        v_opt_5247_,
    );
    lean_dec_ref(v_opt_5247_);
    lean_dec_ref(v_opts_5246_);
    v_r_5249_ = lean_box((v_res_5248_) as usize);
    return v_r_5249_;
}
pub unsafe fn l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
    mut v_x_5250_: *mut LeanObject,
    mut v_x_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5251_) == 0 {
                    v___x_5257_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5257_, 0, v_x_5250_);
                    return v___x_5257_;
                } else {
                    v_head_5258_ = lean_ctor_get(v_x_5251_, 0);
                    lean_inc_n(v_head_5258_, 2);
                    v_tail_5259_ = lean_ctor_get(v_x_5251_, 1);
                    lean_inc(v_tail_5259_);
                    lean_dec_ref_known(v_x_5251_, 2);
                    v___x_5260_ = l_Lean_Expr_mvar___override(v_head_5258_);
                    v___x_5261_ = l_Lean_Meta_getMVars(
                        v___x_5260_,
                        v___y_5252_,
                        v___y_5253_,
                        v___y_5254_,
                        v___y_5255_,
                    );
                    if lean_obj_tag(v___x_5261_) == 0 {
                        v_a_5262_ = lean_ctor_get(v___x_5261_, 0);
                        lean_inc(v_a_5262_);
                        lean_dec_ref_known(v___x_5261_, 1);
                        v___x_5263_ = l_Lean_MVarIdSet_ofArray(v_a_5262_);
                        lean_dec(v_a_5262_);
                        v___x_5264_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MVarIdSet_insert_spec__1___redArg(v_head_5258_, v___x_5263_, v_x_5250_);
                        v_x_5250_ = v___x_5264_;
                        v_x_5251_ = v_tail_5259_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_5259_);
                        lean_dec(v_head_5258_);
                        lean_dec(v_x_5250_);
                        v_a_5266_ = lean_ctor_get(v___x_5261_, 0);
                        v_isSharedCheck_5273_ = (!lean_is_exclusive(v___x_5261_)) as u8;
                        if v_isSharedCheck_5273_ == 0 {
                            v___x_5268_ = v___x_5261_;
                            v_isShared_5269_ = v_isSharedCheck_5273_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5266_);
                            lean_dec(v___x_5261_);
                            v___x_5268_ = lean_box(0);
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
                    v_reuseFailAlloc_5272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5272_, 0, v_a_5266_);
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
    mut v_x_5274_: *mut LeanObject,
    mut v_x_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5281_: *mut LeanObject = core::ptr::null_mut();
    v_res_5281_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
        v_x_5274_,
        v_x_5275_,
        v___y_5276_,
        v___y_5277_,
        v___y_5278_,
        v___y_5279_,
    );
    lean_dec(v___y_5279_);
    lean_dec_ref(v___y_5278_);
    lean_dec(v___y_5277_);
    lean_dec_ref(v___y_5276_);
    return v_res_5281_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(
    mut v_lctx_5282_: *mut LeanObject,
    mut v_localInsts_5283_: *mut LeanObject,
    mut v_x_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
    mut v___y_5287_: *mut LeanObject,
    mut v___y_5288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut v_a_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    lean_box(0),
                    v_lctx_5282_,
                    v_localInsts_5283_,
                    v_x_5284_,
                    v___y_5285_,
                    v___y_5286_,
                    v___y_5287_,
                    v___y_5288_,
                );
                if lean_obj_tag(v___x_5290_) == 0 {
                    v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
                    v_isSharedCheck_5298_ = (!lean_is_exclusive(v___x_5290_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5290_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5291_);
                        lean_dec(v___x_5290_);
                        v___x_5293_ = lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5299_ = lean_ctor_get(v___x_5290_, 0);
                    v_isSharedCheck_5306_ = (!lean_is_exclusive(v___x_5290_)) as u8;
                    if v_isSharedCheck_5306_ == 0 {
                        v___x_5301_ = v___x_5290_;
                        v_isShared_5302_ = v_isSharedCheck_5306_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5299_);
                        lean_dec(v___x_5290_);
                        v___x_5301_ = lean_box(0);
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
                    v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
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
                    v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
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
    mut v_lctx_5307_: *mut LeanObject,
    mut v_localInsts_5308_: *mut LeanObject,
    mut v_x_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_5307_, v_localInsts_5308_, v_x_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
    lean_dec(v___y_5313_);
    lean_dec_ref(v___y_5312_);
    lean_dec(v___y_5311_);
    lean_dec_ref(v___y_5310_);
    return v_res_5315_;
}
pub unsafe fn _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    v___x_5317_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__0;
    v___x_5318_ = l_Lean_stringToMessageData(v___x_5317_);
    return v___x_5318_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(
    mut v_goal_5319_: *mut LeanObject,
    mut v_action_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    v___x_5326_ = lean_st_ref_get(v___y_5322_);
    v_mctx_5327_ = lean_ctor_get(v___x_5326_, 0);
    lean_inc_ref(v_mctx_5327_);
    lean_dec(v___x_5326_);
    v___x_5328_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_5327_, v_goal_5319_);
    lean_dec_ref(v_mctx_5327_);
    if lean_obj_tag(v___x_5328_) == 1 {
        let mut v_val_5329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_options_5330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lctx_5331_: *mut LeanObject = core::ptr::null_mut();
        let mut v_localInstances_5332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_5336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_goal_5319_);
        v_val_5329_ = lean_ctor_get(v___x_5328_, 0);
        lean_inc(v_val_5329_);
        lean_dec_ref_known(v___x_5328_, 1);
        v_options_5330_ = lean_ctor_get(v___y_5323_, 2);
        v_lctx_5331_ = lean_ctor_get(v_val_5329_, 1);
        v_localInstances_5332_ = lean_ctor_get(v_val_5329_, 4);
        lean_inc_ref(v_localInstances_5332_);
        v___x_5333_ = lean_box(1);
        lean_inc_ref(v_options_5330_);
        v___x_5334_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_5334_, 0, v_options_5330_);
        lean_ctor_set(v___x_5334_, 1, v___x_5333_);
        lean_ctor_set(v___x_5334_, 2, v___x_5333_);
        lean_inc_ref(v_lctx_5331_);
        v___x_5335_ = l_Lean_LocalContext_sanitizeNames(v_lctx_5331_, v___x_5334_);
        v_fst_5336_ = lean_ctor_get(v___x_5335_, 0);
        lean_inc_n(v_fst_5336_, 2);
        lean_dec_ref(v___x_5335_);
        v___x_5337_ = lean_apply_2(v_action_5320_, v_fst_5336_, v_val_5329_);
        v___x_5338_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_fst_5336_, v_localInstances_5332_, v___x_5337_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
        return v___x_5338_;
    } else {
        let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_5328_);
        lean_dec_ref(v_action_5320_);
        v___x_5339_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1_once), _init_l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___closed__1);
        v___x_5340_ = l_Lean_MessageData_ofName(v_goal_5319_);
        v___x_5341_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_5341_, 0, v___x_5339_);
        lean_ctor_set(v___x_5341_, 1, v___x_5340_);
        v___x_5342_ = l_Lean_throwError___at___00__private_Lean_Widget_Diff_0__Lean_Widget_exprDiffCore_piDiff_spec__3___redArg(v___x_5341_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
        return v___x_5342_;
    }
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg___boxed(
    mut v_goal_5343_: *mut LeanObject,
    mut v_action_5344_: *mut LeanObject,
    mut v___y_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5350_: *mut LeanObject = core::ptr::null_mut();
    v_res_5350_ =
        l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(
            v_goal_5343_,
            v_action_5344_,
            v___y_5345_,
            v___y_5346_,
            v___y_5347_,
            v___y_5348_,
        );
    lean_dec(v___y_5348_);
    lean_dec_ref(v___y_5347_);
    lean_dec(v___y_5346_);
    lean_dec_ref(v___y_5345_);
    return v_res_5350_;
}
pub unsafe fn l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(
    mut v___x_5351_: *mut LeanObject,
    mut v_x_5352_: *mut LeanObject,
) -> u8 {
    let mut v___x_5353_: u8 = 0;
    let mut v_head_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5352_) == 0 {
                    v___x_5353_ = 0;
                    return v___x_5353_;
                } else {
                    v_head_5354_ = lean_ctor_get(v_x_5352_, 0);
                    v_tail_5355_ = lean_ctor_get(v_x_5352_, 1);
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
    mut v___x_5358_: *mut LeanObject,
    mut v_x_5359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5360_: u8 = 0;
    let mut v_r_5361_: *mut LeanObject = core::ptr::null_mut();
    v_res_5360_ =
        l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v___x_5358_, v_x_5359_);
    lean_dec(v_x_5359_);
    lean_dec(v___x_5358_);
    v_r_5361_ = lean_box((v_res_5360_) as usize);
    return v_r_5361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(
    mut v_t_5362_: *mut LeanObject,
    mut v_k_5363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: u8 = 0;
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5362_) == 0 {
                    v_k_5364_ = lean_ctor_get(v_t_5362_, 1);
                    v_v_5365_ = lean_ctor_get(v_t_5362_, 2);
                    v_l_5366_ = lean_ctor_get(v_t_5362_, 3);
                    v_r_5367_ = lean_ctor_get(v_t_5362_, 4);
                    v___x_5368_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5363_, v_k_5364_);
                    match v___x_5368_ {
                        0 => {
                            v_t_5362_ = v_l_5366_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_5365_);
                            v___x_5370_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5370_, 0, v_v_5365_);
                            return v___x_5370_;
                        }
                        _ => {
                            v_t_5362_ = v_r_5367_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5372_ = lean_box(0);
                    return v___x_5372_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg___boxed(
    mut v_t_5373_: *mut LeanObject,
    mut v_k_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5375_: *mut LeanObject = core::ptr::null_mut();
    v_res_5375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_5373_, v_k_5374_);
    lean_dec(v_k_5374_);
    lean_dec(v_t_5373_);
    return v_res_5375_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(
    mut v_k_5376_: *mut LeanObject,
    mut v_t_5377_: *mut LeanObject,
) -> u8 {
    let mut v_k_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5383_: u8 = 0;
    let mut v___x_5385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5377_) == 0 {
                    v_k_5378_ = lean_ctor_get(v_t_5377_, 1);
                    v_l_5379_ = lean_ctor_get(v_t_5377_, 3);
                    v_r_5380_ = lean_ctor_get(v_t_5377_, 4);
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
    mut v_k_5386_: *mut LeanObject,
    mut v_t_5387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5388_: u8 = 0;
    let mut v_r_5389_: *mut LeanObject = core::ptr::null_mut();
    v_res_5388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_5386_, v_t_5387_);
    lean_dec(v_t_5387_);
    lean_dec(v_k_5386_);
    v_r_5389_ = lean_box((v_res_5388_) as usize);
    return v_r_5389_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(
    mut v_a_5390_: *mut LeanObject,
    mut v___x_5391_: u8,
    mut v_before_5392_: *mut LeanObject,
    mut v_after_5393_: *mut LeanObject,
) -> u8 {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_a_5390_, v_before_5392_);
    if lean_obj_tag(v___x_5394_) == 0 {
        return v___x_5391_;
    } else {
        let mut v_val_5395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5396_: u8 = 0;
        v_val_5395_ = lean_ctor_get(v___x_5394_, 0);
        lean_inc(v_val_5395_);
        lean_dec_ref_known(v___x_5394_, 1);
        v___x_5396_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_after_5393_, v_val_5395_);
        lean_dec(v_val_5395_);
        return v___x_5396_;
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0___boxed(
    mut v_a_5397_: *mut LeanObject,
    mut v___x_5398_: *mut LeanObject,
    mut v_before_5399_: *mut LeanObject,
    mut v_after_5400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3864__boxed_5401_: u8 = 0;
    let mut v_res_5402_: u8 = 0;
    let mut v_r_5403_: *mut LeanObject = core::ptr::null_mut();
    v___x_3864__boxed_5401_ = (lean_unbox(v___x_5398_) as u8);
    v_res_5402_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___lam__0(
        v_a_5397_,
        v___x_3864__boxed_5401_,
        v_before_5399_,
        v_after_5400_,
    );
    lean_dec(v_after_5400_);
    lean_dec(v_before_5399_);
    lean_dec(v_a_5397_);
    v_r_5403_ = lean_box((v_res_5402_) as usize);
    return v_r_5403_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
    mut v___y_5404_: u8,
    mut v_a_5405_: *mut LeanObject,
    mut v___x_5406_: *mut LeanObject,
    mut v_x_5407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: u8 = 0;
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: u8 = 0;
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5407_) == 0 {
                    v___x_5408_ = lean_box(0);
                    return v___x_5408_;
                } else {
                    v_head_5409_ = lean_ctor_get(v_x_5407_, 0);
                    v_tail_5410_ = lean_ctor_get(v_x_5407_, 1);
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
                    lean_inc(v_head_5409_);
                    v___x_5414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5414_, 0, v_head_5409_);
                    return v___x_5414_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5___boxed(
    mut v___y_5418_: *mut LeanObject,
    mut v_a_5419_: *mut LeanObject,
    mut v___x_5420_: *mut LeanObject,
    mut v_x_5421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3875__boxed_5422_: u8 = 0;
    let mut v_res_5423_: *mut LeanObject = core::ptr::null_mut();
    v___y_3875__boxed_5422_ = (lean_unbox(v___y_5418_) as u8);
    v_res_5423_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
        v___y_3875__boxed_5422_,
        v_a_5419_,
        v___x_5420_,
        v_x_5421_,
    );
    lean_dec(v_x_5421_);
    lean_dec(v___x_5420_);
    lean_dec(v_a_5419_);
    return v_res_5423_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(
    mut v_mvarId_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: u8,
    mut v_a_5427_: *mut LeanObject,
    mut v_useAfter_5428_: u8,
    mut v_v_5429_: *mut LeanObject,
    mut v___x_5430_: u8,
    mut v_toInteractiveGoalCore_5431_: *mut LeanObject,
    mut v_userName_x3f_5432_: *mut LeanObject,
    mut v_goalPrefix_5433_: *mut LeanObject,
    mut v_isInserted_x3f_5434_: *mut LeanObject,
    mut v_isRemoved_x3f_5435_: *mut LeanObject,
    mut v___lctx_u2081_5436_: *mut LeanObject,
    mut v___md_u2081_5437_: *mut LeanObject,
    mut v___y_5438_: *mut LeanObject,
    mut v___y_5439_: *mut LeanObject,
    mut v___y_5440_: *mut LeanObject,
    mut v___y_5441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5443_: u8 = 0;
    v___x_5443_ =
        l_List_any___at___00Lean_Widget_diffInteractiveGoals_spec__4(v_mvarId_5424_, v___y_5425_);
    if v___x_5443_ == 0 {
        let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
        v___x_5444_ = l_List_find_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__5(
            v___y_5426_,
            v_a_5427_,
            v_mvarId_5424_,
            v___y_5425_,
        );
        if lean_obj_tag(v___x_5444_) == 1 {
            let mut v_val_5445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_isRemoved_x3f_5435_);
            lean_dec(v_isInserted_x3f_5434_);
            lean_dec_ref(v_goalPrefix_5433_);
            lean_dec(v_userName_x3f_5432_);
            lean_dec_ref(v_toInteractiveGoalCore_5431_);
            lean_dec(v_mvarId_5424_);
            v_val_5445_ = lean_ctor_get(v___x_5444_, 0);
            lean_inc(v_val_5445_);
            lean_dec_ref_known(v___x_5444_, 1);
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
            lean_dec(v___x_5444_);
            lean_dec(v_v_5429_);
            if v___y_5426_ == 0 {
                let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_isRemoved_x3f_5435_);
                v___x_5447_ = lean_box((v___x_5430_) as usize);
                v___x_5448_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5448_, 0, v___x_5447_);
                v___x_5449_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_5449_, 0, v_toInteractiveGoalCore_5431_);
                lean_ctor_set(v___x_5449_, 1, v_userName_x3f_5432_);
                lean_ctor_set(v___x_5449_, 2, v_goalPrefix_5433_);
                lean_ctor_set(v___x_5449_, 3, v_mvarId_5424_);
                lean_ctor_set(v___x_5449_, 4, v_isInserted_x3f_5434_);
                lean_ctor_set(v___x_5449_, 5, v___x_5448_);
                v___x_5450_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5450_, 0, v___x_5449_);
                return v___x_5450_;
            } else {
                let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_isInserted_x3f_5434_);
                v___x_5451_ = lean_box((v___x_5430_) as usize);
                v___x_5452_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5452_, 0, v___x_5451_);
                v___x_5453_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_5453_, 0, v_toInteractiveGoalCore_5431_);
                lean_ctor_set(v___x_5453_, 1, v_userName_x3f_5432_);
                lean_ctor_set(v___x_5453_, 2, v_goalPrefix_5433_);
                lean_ctor_set(v___x_5453_, 3, v_mvarId_5424_);
                lean_ctor_set(v___x_5453_, 4, v___x_5452_);
                lean_ctor_set(v___x_5453_, 5, v_isRemoved_x3f_5435_);
                v___x_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                return v___x_5454_;
            }
        }
    } else {
        let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_isInserted_x3f_5434_);
        lean_dec(v_v_5429_);
        v___x_5455_ = lean_box(0);
        v___x_5456_ = lean_alloc_ctor(0, 6, (0) as u32);
        lean_ctor_set(v___x_5456_, 0, v_toInteractiveGoalCore_5431_);
        lean_ctor_set(v___x_5456_, 1, v_userName_x3f_5432_);
        lean_ctor_set(v___x_5456_, 2, v_goalPrefix_5433_);
        lean_ctor_set(v___x_5456_, 3, v_mvarId_5424_);
        lean_ctor_set(v___x_5456_, 4, v___x_5455_);
        lean_ctor_set(v___x_5456_, 5, v_isRemoved_x3f_5435_);
        v___x_5457_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5457_, 0, v___x_5456_);
        return v___x_5457_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mvarId_5458_: *mut LeanObject = *_args.add(0);
    let mut v___y_5459_: *mut LeanObject = *_args.add(1);
    let mut v___y_5460_: *mut LeanObject = *_args.add(2);
    let mut v_a_5461_: *mut LeanObject = *_args.add(3);
    let mut v_useAfter_5462_: *mut LeanObject = *_args.add(4);
    let mut v_v_5463_: *mut LeanObject = *_args.add(5);
    let mut v___x_5464_: *mut LeanObject = *_args.add(6);
    let mut v_toInteractiveGoalCore_5465_: *mut LeanObject = *_args.add(7);
    let mut v_userName_x3f_5466_: *mut LeanObject = *_args.add(8);
    let mut v_goalPrefix_5467_: *mut LeanObject = *_args.add(9);
    let mut v_isInserted_x3f_5468_: *mut LeanObject = *_args.add(10);
    let mut v_isRemoved_x3f_5469_: *mut LeanObject = *_args.add(11);
    let mut v___lctx_u2081_5470_: *mut LeanObject = *_args.add(12);
    let mut v___md_u2081_5471_: *mut LeanObject = *_args.add(13);
    let mut v___y_5472_: *mut LeanObject = *_args.add(14);
    let mut v___y_5473_: *mut LeanObject = *_args.add(15);
    let mut v___y_5474_: *mut LeanObject = *_args.add(16);
    let mut v___y_5475_: *mut LeanObject = *_args.add(17);
    let mut v___y_5476_: *mut LeanObject = *_args.add(18);
    let mut v___y_3908__boxed_5477_: u8 = 0;
    let mut v_useAfter_boxed_5478_: u8 = 0;
    let mut v___x_3910__boxed_5479_: u8 = 0;
    let mut v_res_5480_: *mut LeanObject = core::ptr::null_mut();
    v___y_3908__boxed_5477_ = (lean_unbox(v___y_5460_) as u8);
    v_useAfter_boxed_5478_ = (lean_unbox(v_useAfter_5462_) as u8);
    v___x_3910__boxed_5479_ = (lean_unbox(v___x_5464_) as u8);
    v_res_5480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0(v_mvarId_5458_, v___y_5459_, v___y_3908__boxed_5477_, v_a_5461_, v_useAfter_boxed_5478_, v_v_5463_, v___x_3910__boxed_5479_, v_toInteractiveGoalCore_5465_, v_userName_x3f_5466_, v_goalPrefix_5467_, v_isInserted_x3f_5468_, v_isRemoved_x3f_5469_, v___lctx_u2081_5470_, v___md_u2081_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
    lean_dec(v___y_5475_);
    lean_dec_ref(v___y_5474_);
    lean_dec(v___y_5473_);
    lean_dec_ref(v___y_5472_);
    lean_dec_ref(v___md_u2081_5471_);
    lean_dec_ref(v___lctx_u2081_5470_);
    lean_dec(v_a_5461_);
    lean_dec(v___y_5459_);
    return v_res_5480_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: u8,
    mut v_a_5483_: *mut LeanObject,
    mut v_useAfter_5484_: u8,
    mut v___x_5485_: u8,
    mut v_sz_5486_: usize,
    mut v_i_5487_: usize,
    mut v_bs_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
    mut v___y_5491_: *mut LeanObject,
    mut v___y_5492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5494_: u8 = 0;
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: usize = 0;
    let mut v___x_5512_: usize = 0;
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5518_: u8 = 0;
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5494_ = lean_usize_dec_lt(v_i_5487_, v_sz_5486_);
                if v___x_5494_ == 0 {
                    lean_dec(v_a_5483_);
                    lean_dec(v___y_5481_);
                    v___x_5495_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5495_, 0, v_bs_5488_);
                    return v___x_5495_;
                } else {
                    v_v_5496_ = lean_array_uget_borrowed(v_bs_5488_, v_i_5487_);
                    v_toInteractiveGoalCore_5497_ = lean_ctor_get(v_v_5496_, 0);
                    v_userName_x3f_5498_ = lean_ctor_get(v_v_5496_, 1);
                    v_goalPrefix_5499_ = lean_ctor_get(v_v_5496_, 2);
                    v_mvarId_5500_ = lean_ctor_get(v_v_5496_, 3);
                    v_isInserted_x3f_5501_ = lean_ctor_get(v_v_5496_, 4);
                    v_isRemoved_x3f_5502_ = lean_ctor_get(v_v_5496_, 5);
                    v___x_5503_ = lean_box((v___y_5482_) as usize);
                    v___x_5504_ = lean_box((v_useAfter_5484_) as usize);
                    v___x_5505_ = lean_box((v___x_5485_) as usize);
                    lean_inc(v_isRemoved_x3f_5502_);
                    lean_inc(v_isInserted_x3f_5501_);
                    lean_inc_ref(v_goalPrefix_5499_);
                    lean_inc(v_userName_x3f_5498_);
                    lean_inc_ref(v_toInteractiveGoalCore_5497_);
                    lean_inc(v_v_5496_);
                    lean_inc(v_a_5483_);
                    lean_inc(v___y_5481_);
                    lean_inc_n(v_mvarId_5500_, 2);
                    v___f_5506_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed as *mut core::ffi::c_void, 19, 12);
                    lean_closure_set(v___f_5506_, 0, v_mvarId_5500_);
                    lean_closure_set(v___f_5506_, 1, v___y_5481_);
                    lean_closure_set(v___f_5506_, 2, v___x_5503_);
                    lean_closure_set(v___f_5506_, 3, v_a_5483_);
                    lean_closure_set(v___f_5506_, 4, v___x_5504_);
                    lean_closure_set(v___f_5506_, 5, v_v_5496_);
                    lean_closure_set(v___f_5506_, 6, v___x_5505_);
                    lean_closure_set(v___f_5506_, 7, v_toInteractiveGoalCore_5497_);
                    lean_closure_set(v___f_5506_, 8, v_userName_x3f_5498_);
                    lean_closure_set(v___f_5506_, 9, v_goalPrefix_5499_);
                    lean_closure_set(v___f_5506_, 10, v_isInserted_x3f_5501_);
                    lean_closure_set(v___f_5506_, 11, v_isRemoved_x3f_5502_);
                    v___x_5507_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_5500_, v___f_5506_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
                    if lean_obj_tag(v___x_5507_) == 0 {
                        v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
                        lean_inc(v_a_5508_);
                        lean_dec_ref_known(v___x_5507_, 1);
                        v___x_5509_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5510_ = lean_array_uset(v_bs_5488_, v_i_5487_, v___x_5509_);
                        v___x_5511_ = 1usize;
                        v___x_5512_ = lean_usize_add(v_i_5487_, v___x_5511_);
                        v___x_5513_ = lean_array_uset(v_bs_x27_5510_, v_i_5487_, v_a_5508_);
                        v_i_5487_ = v___x_5512_;
                        v_bs_5488_ = v___x_5513_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5488_);
                        lean_dec(v_a_5483_);
                        lean_dec(v___y_5481_);
                        v_a_5515_ = lean_ctor_get(v___x_5507_, 0);
                        v_isSharedCheck_5522_ = (!lean_is_exclusive(v___x_5507_)) as u8;
                        if v_isSharedCheck_5522_ == 0 {
                            v___x_5517_ = v___x_5507_;
                            v_isShared_5518_ = v_isSharedCheck_5522_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5515_);
                            lean_dec(v___x_5507_);
                            v___x_5517_ = lean_box(0);
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
                    v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
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
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
    mut v_a_5525_: *mut LeanObject,
    mut v_useAfter_5526_: *mut LeanObject,
    mut v___x_5527_: *mut LeanObject,
    mut v_sz_5528_: *mut LeanObject,
    mut v_i_5529_: *mut LeanObject,
    mut v_bs_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3965__boxed_5536_: u8 = 0;
    let mut v_useAfter_boxed_5537_: u8 = 0;
    let mut v___x_3967__boxed_5538_: u8 = 0;
    let mut v_sz_boxed_5539_: usize = 0;
    let mut v_i_boxed_5540_: usize = 0;
    let mut v_res_5541_: *mut LeanObject = core::ptr::null_mut();
    v___y_3965__boxed_5536_ = (lean_unbox(v___y_5524_) as u8);
    v_useAfter_boxed_5537_ = (lean_unbox(v_useAfter_5526_) as u8);
    v___x_3967__boxed_5538_ = (lean_unbox(v___x_5527_) as u8);
    v_sz_boxed_5539_ = lean_unbox_usize(v_sz_5528_);
    lean_dec(v_sz_5528_);
    v_i_boxed_5540_ = lean_unbox_usize(v_i_5529_);
    lean_dec(v_i_5529_);
    v_res_5541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_5523_, v___y_3965__boxed_5536_, v_a_5525_, v_useAfter_boxed_5537_, v___x_3967__boxed_5538_, v_sz_boxed_5539_, v_i_boxed_5540_, v_bs_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
    lean_dec(v___y_5534_);
    lean_dec_ref(v___y_5533_);
    lean_dec(v___y_5532_);
    lean_dec_ref(v___y_5531_);
    return v_res_5541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(
    mut v___y_5542_: u8,
    mut v_a_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v_useAfter_5545_: u8,
    mut v___x_5546_: u8,
    mut v_sz_5547_: usize,
    mut v_i_5548_: usize,
    mut v_bs_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
    mut v___y_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInteractiveGoalCore_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: usize = 0;
    let mut v___x_5573_: usize = 0;
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5579_: u8 = 0;
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5555_ = lean_usize_dec_lt(v_i_5548_, v_sz_5547_);
                if v___x_5555_ == 0 {
                    lean_dec(v___y_5544_);
                    lean_dec(v_a_5543_);
                    v___x_5556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5556_, 0, v_bs_5549_);
                    return v___x_5556_;
                } else {
                    v_v_5557_ = lean_array_uget_borrowed(v_bs_5549_, v_i_5548_);
                    v_toInteractiveGoalCore_5558_ = lean_ctor_get(v_v_5557_, 0);
                    v_userName_x3f_5559_ = lean_ctor_get(v_v_5557_, 1);
                    v_goalPrefix_5560_ = lean_ctor_get(v_v_5557_, 2);
                    v_mvarId_5561_ = lean_ctor_get(v_v_5557_, 3);
                    v_isInserted_x3f_5562_ = lean_ctor_get(v_v_5557_, 4);
                    v_isRemoved_x3f_5563_ = lean_ctor_get(v_v_5557_, 5);
                    v___x_5564_ = lean_box((v___y_5542_) as usize);
                    v___x_5565_ = lean_box((v_useAfter_5545_) as usize);
                    v___x_5566_ = lean_box((v___x_5546_) as usize);
                    lean_inc(v_isRemoved_x3f_5563_);
                    lean_inc(v_isInserted_x3f_5562_);
                    lean_inc_ref(v_goalPrefix_5560_);
                    lean_inc(v_userName_x3f_5559_);
                    lean_inc_ref(v_toInteractiveGoalCore_5558_);
                    lean_inc(v_v_5557_);
                    lean_inc(v_a_5543_);
                    lean_inc(v___y_5544_);
                    lean_inc_n(v_mvarId_5561_, 2);
                    v___f_5567_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7___lam__0___boxed as *mut core::ffi::c_void, 19, 12);
                    lean_closure_set(v___f_5567_, 0, v_mvarId_5561_);
                    lean_closure_set(v___f_5567_, 1, v___y_5544_);
                    lean_closure_set(v___f_5567_, 2, v___x_5564_);
                    lean_closure_set(v___f_5567_, 3, v_a_5543_);
                    lean_closure_set(v___f_5567_, 4, v___x_5565_);
                    lean_closure_set(v___f_5567_, 5, v_v_5557_);
                    lean_closure_set(v___f_5567_, 6, v___x_5566_);
                    lean_closure_set(v___f_5567_, 7, v_toInteractiveGoalCore_5558_);
                    lean_closure_set(v___f_5567_, 8, v_userName_x3f_5559_);
                    lean_closure_set(v___f_5567_, 9, v_goalPrefix_5560_);
                    lean_closure_set(v___f_5567_, 10, v_isInserted_x3f_5562_);
                    lean_closure_set(v___f_5567_, 11, v_isRemoved_x3f_5563_);
                    v___x_5568_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6___redArg(v_mvarId_5561_, v___f_5567_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
                    if lean_obj_tag(v___x_5568_) == 0 {
                        v_a_5569_ = lean_ctor_get(v___x_5568_, 0);
                        lean_inc(v_a_5569_);
                        lean_dec_ref_known(v___x_5568_, 1);
                        v___x_5570_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5571_ = lean_array_uset(v_bs_5549_, v_i_5548_, v___x_5570_);
                        v___x_5572_ = 1usize;
                        v___x_5573_ = lean_usize_add(v_i_5548_, v___x_5572_);
                        v___x_5574_ = lean_array_uset(v_bs_x27_5571_, v_i_5548_, v_a_5569_);
                        v___x_5575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7_spec__8(v___y_5544_, v___y_5542_, v_a_5543_, v_useAfter_5545_, v___x_5546_, v_sz_5547_, v___x_5573_, v___x_5574_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
                        return v___x_5575_;
                    } else {
                        lean_dec_ref(v_bs_5549_);
                        lean_dec(v___y_5544_);
                        lean_dec(v_a_5543_);
                        v_a_5576_ = lean_ctor_get(v___x_5568_, 0);
                        v_isSharedCheck_5583_ = (!lean_is_exclusive(v___x_5568_)) as u8;
                        if v_isSharedCheck_5583_ == 0 {
                            v___x_5578_ = v___x_5568_;
                            v_isShared_5579_ = v_isSharedCheck_5583_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5576_);
                            lean_dec(v___x_5568_);
                            v___x_5578_ = lean_box(0);
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
                    v_reuseFailAlloc_5582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
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
    mut v___y_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v_useAfter_5587_: *mut LeanObject,
    mut v___x_5588_: *mut LeanObject,
    mut v_sz_5589_: *mut LeanObject,
    mut v_i_5590_: *mut LeanObject,
    mut v_bs_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
    mut v___y_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4033__boxed_5597_: u8 = 0;
    let mut v_useAfter_boxed_5598_: u8 = 0;
    let mut v___x_4036__boxed_5599_: u8 = 0;
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut LeanObject = core::ptr::null_mut();
    v___y_4033__boxed_5597_ = (lean_unbox(v___y_5584_) as u8);
    v_useAfter_boxed_5598_ = (lean_unbox(v_useAfter_5587_) as u8);
    v___x_4036__boxed_5599_ = (lean_unbox(v___x_5588_) as u8);
    v_sz_boxed_5600_ = lean_unbox_usize(v_sz_5589_);
    lean_dec(v_sz_5589_);
    v_i_boxed_5601_ = lean_unbox_usize(v_i_5590_);
    lean_dec(v_i_5590_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v___y_4033__boxed_5597_, v_a_5585_, v___y_5586_, v_useAfter_boxed_5598_, v___x_4036__boxed_5599_, v_sz_boxed_5600_, v_i_boxed_5601_, v_bs_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    lean_dec(v___y_5595_);
    lean_dec_ref(v___y_5594_);
    lean_dec(v___y_5593_);
    lean_dec_ref(v___y_5592_);
    return v_res_5602_;
}
pub unsafe fn l_Lean_Widget_diffInteractiveGoals(
    mut v_useAfter_5603_: u8,
    mut v_info_5604_: *mut LeanObject,
    mut v_igs_u2081_5605_: *mut LeanObject,
    mut v_a_5606_: *mut LeanObject,
    mut v_a_5607_: *mut LeanObject,
    mut v_a_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: u8 = 0;
    let mut v___y_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5620_: usize = 0;
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_a_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v___x_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsAfter_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goalsBefore_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5611_ = lean_ctor_get(v_a_5608_, 2);
                v___x_5612_ = l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff;
                v___x_5613_ = l_Lean_Option_get___at___00Lean_Widget_diffInteractiveGoals_spec__0(
                    v_options_5611_,
                    v___x_5612_,
                );
                if v___x_5613_ == 0 {
                    lean_dec_ref(v_info_5604_);
                    v___x_5647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5647_, 0, v_igs_u2081_5605_);
                    return v___x_5647_;
                } else {
                    if v_useAfter_5603_ == 0 {
                        v_goalsAfter_5648_ = lean_ctor_get(v_info_5604_, 4);
                        lean_inc(v_goalsAfter_5648_);
                        v___y_5615_ = v_goalsAfter_5648_;
                        state = 1;
                        continue;
                    } else {
                        v_goalsBefore_5649_ = lean_ctor_get(v_info_5604_, 2);
                        lean_inc(v_goalsBefore_5649_);
                        v___y_5615_ = v_goalsBefore_5649_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_goalsBefore_5616_ = lean_ctor_get(v_info_5604_, 2);
                lean_inc(v_goalsBefore_5616_);
                lean_dec_ref(v_info_5604_);
                v___x_5617_ = lean_box(1);
                v___x_5618_ = l_List_foldlM___at___00Lean_Widget_diffInteractiveGoals_spec__1(
                    v___x_5617_,
                    v_goalsBefore_5616_,
                    v_a_5606_,
                    v_a_5607_,
                    v_a_5608_,
                    v_a_5609_,
                );
                if lean_obj_tag(v___x_5618_) == 0 {
                    v_a_5619_ = lean_ctor_get(v___x_5618_, 0);
                    lean_inc(v_a_5619_);
                    lean_dec_ref_known(v___x_5618_, 1);
                    v_sz_5620_ = lean_array_size(v_igs_u2081_5605_);
                    v___x_5621_ = 0usize;
                    v___x_5622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_diffInteractiveGoals_spec__7(v_useAfter_5603_, v_a_5619_, v___y_5615_, v_useAfter_5603_, v___x_5613_, v_sz_5620_, v___x_5621_, v_igs_u2081_5605_, v_a_5606_, v_a_5607_, v_a_5608_, v_a_5609_);
                    if lean_obj_tag(v___x_5622_) == 0 {
                        v_a_5623_ = lean_ctor_get(v___x_5622_, 0);
                        v_isSharedCheck_5630_ = (!lean_is_exclusive(v___x_5622_)) as u8;
                        if v_isSharedCheck_5630_ == 0 {
                            v___x_5625_ = v___x_5622_;
                            v_isShared_5626_ = v_isSharedCheck_5630_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5623_);
                            lean_dec(v___x_5622_);
                            v___x_5625_ = lean_box(0);
                            v_isShared_5626_ = v_isSharedCheck_5630_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5631_ = lean_ctor_get(v___x_5622_, 0);
                        v_isSharedCheck_5638_ = (!lean_is_exclusive(v___x_5622_)) as u8;
                        if v_isSharedCheck_5638_ == 0 {
                            v___x_5633_ = v___x_5622_;
                            v_isShared_5634_ = v_isSharedCheck_5638_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5631_);
                            lean_dec(v___x_5622_);
                            v___x_5633_ = lean_box(0);
                            v_isShared_5634_ = v_isSharedCheck_5638_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5615_);
                    lean_dec_ref(v_igs_u2081_5605_);
                    v_a_5639_ = lean_ctor_get(v___x_5618_, 0);
                    v_isSharedCheck_5646_ = (!lean_is_exclusive(v___x_5618_)) as u8;
                    if v_isSharedCheck_5646_ == 0 {
                        v___x_5641_ = v___x_5618_;
                        v_isShared_5642_ = v_isSharedCheck_5646_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5639_);
                        lean_dec(v___x_5618_);
                        v___x_5641_ = lean_box(0);
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
                    v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
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
                    v_reuseFailAlloc_5637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
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
                    v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
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
    mut v_useAfter_5650_: *mut LeanObject,
    mut v_info_5651_: *mut LeanObject,
    mut v_igs_u2081_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_a_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
    mut v_a_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useAfter_boxed_5658_: u8 = 0;
    let mut v_res_5659_: *mut LeanObject = core::ptr::null_mut();
    v_useAfter_boxed_5658_ = (lean_unbox(v_useAfter_5650_) as u8);
    v_res_5659_ = l_Lean_Widget_diffInteractiveGoals(
        v_useAfter_boxed_5658_,
        v_info_5651_,
        v_igs_u2081_5652_,
        v_a_5653_,
        v_a_5654_,
        v_a_5655_,
        v_a_5656_,
    );
    lean_dec(v_a_5656_);
    lean_dec_ref(v_a_5655_);
    lean_dec(v_a_5654_);
    lean_dec_ref(v_a_5653_);
    return v_res_5659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(
    mut v_00_u03b4_5660_: *mut LeanObject,
    mut v_t_5661_: *mut LeanObject,
    mut v_k_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    v___x_5663_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___redArg(v_t_5661_, v_k_5662_);
    return v___x_5663_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2___boxed(
    mut v_00_u03b4_5664_: *mut LeanObject,
    mut v_t_5665_: *mut LeanObject,
    mut v_k_5666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5667_: *mut LeanObject = core::ptr::null_mut();
    v_res_5667_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Widget_diffInteractiveGoals_spec__2(v_00_u03b4_5664_, v_t_5665_, v_k_5666_);
    lean_dec(v_k_5666_);
    lean_dec(v_t_5665_);
    return v_res_5667_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(
    mut v_00_u03b2_5668_: *mut LeanObject,
    mut v_k_5669_: *mut LeanObject,
    mut v_t_5670_: *mut LeanObject,
) -> u8 {
    let mut v___x_5671_: u8 = 0;
    v___x_5671_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___redArg(v_k_5669_, v_t_5670_);
    return v___x_5671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3___boxed(
    mut v_00_u03b2_5672_: *mut LeanObject,
    mut v_k_5673_: *mut LeanObject,
    mut v_t_5674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5675_: u8 = 0;
    let mut v_r_5676_: *mut LeanObject = core::ptr::null_mut();
    v_res_5675_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Widget_diffInteractiveGoals_spec__3(
            v_00_u03b2_5672_,
            v_k_5673_,
            v_t_5674_,
        );
    lean_dec(v_t_5674_);
    lean_dec(v_k_5673_);
    v_r_5676_ = lean_box((v_res_5675_) as usize);
    return v_r_5676_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(
    mut v_00_u03b1_5677_: *mut LeanObject,
    mut v_lctx_5678_: *mut LeanObject,
    mut v_localInsts_5679_: *mut LeanObject,
    mut v_x_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___redArg(v_lctx_5678_, v_localInsts_5679_, v_x_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    return v___x_5686_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6___boxed(
    mut v_00_u03b1_5687_: *mut LeanObject,
    mut v_lctx_5688_: *mut LeanObject,
    mut v_localInsts_5689_: *mut LeanObject,
    mut v_x_5690_: *mut LeanObject,
    mut v___y_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5696_: *mut LeanObject = core::ptr::null_mut();
    v_res_5696_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6_spec__6(v_00_u03b1_5687_, v_lctx_5688_, v_localInsts_5689_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
    lean_dec(v___y_5694_);
    lean_dec_ref(v___y_5693_);
    lean_dec(v___y_5692_);
    lean_dec_ref(v___y_5691_);
    return v_res_5696_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(
    mut v_00_u03b1_5697_: *mut LeanObject,
    mut v_goal_5698_: *mut LeanObject,
    mut v_action_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5706_: *mut LeanObject,
    mut v_goal_5707_: *mut LeanObject,
    mut v_action_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5714_: *mut LeanObject = core::ptr::null_mut();
    v_res_5714_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_diffInteractiveGoals_spec__6(
        v_00_u03b1_5706_,
        v_goal_5707_,
        v_action_5708_,
        v___y_5709_,
        v___y_5710_,
        v___y_5711_,
        v___y_5712_,
    );
    lean_dec(v___y_5712_);
    lean_dec_ref(v___y_5711_);
    lean_dec(v___y_5710_);
    lean_dec_ref(v___y_5709_);
    return v_res_5714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_Diff(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Widget_Diff_0__Lean_Widget_initFn_00___x40_Lean_Widget_Diff_2925400476____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Widget_Diff_0__Lean_Widget_showTacticDiff);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_Diff(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_Diff(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_InteractiveGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Diff(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_Diff(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Widget_Diff(builtin);
}
