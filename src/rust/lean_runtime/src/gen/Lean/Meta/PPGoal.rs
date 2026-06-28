// Lean compiler output
// Module: Lean.Meta.PPGoal
// Imports: Lean.Meta.InferType
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_isNil;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6, lean_erase_macro_scopes, lean_simp_macro_scopes,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_approxDepth, l_Lean_Expr_hasMVar, l_Lean_Expr_isAtomic, l_Lean_isLHSGoal_x3f,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_sanitizeNames, l_Lean_LocalDecl_isAuxDecl,
    l_Lean_LocalDecl_isImplementationDetail,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp, l_Lean_Meta_ppExpr,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findDecl_x3f, l_Lean_MetavarKind_isSyntheticOpaque,
    l_Lean_instantiateMVarsCore,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_uint32_to_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 117, 120, 68, 101, 99, 108, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,13792545823603790118 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [100, 105, 115, 112, 108, 97, 121, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 117, 115, 101, 100, 32, 116, 111, 32, 99, 111, 109, 112, 105, 108, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,1089554366500606663 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 68, 101, 116, 97, 105, 108, 72, 121, 112, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject,10139256878412505439 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value: LeanStringObject<62> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [100, 105, 115, 112, 108, 97, 121, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 100, 101, 116, 97, 105, 108, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject,5951203697350016830 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 78, 97, 109, 101, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject,16752118453198561512 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [100, 105, 115, 112, 108, 97, 121, 32, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 105, 110, 32, 116, 104, 101, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject,9347561426026548401 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,3655157751251404823 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 108, 119, 97, 121, 115, 32, 100, 105, 115, 112, 108, 97, 121, 32, 108, 101, 116, 45, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 118, 97, 108, 117, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 105, 110, 102, 111, 32, 118, 105, 101, 119, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,2999604245836119670 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,3655157751251404823 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject,9220132061368880167 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value: LeanStringObject<100> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 97, m_data: [119, 104, 101, 110, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 116, 104, 101, 32, 109, 97, 120, 105, 109, 117, 109, 32, 115, 105, 122, 101, 32, 111, 102, 32, 97, 32, 116, 101, 114, 109, 32, 97, 108, 108, 111, 119, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 105, 116, 32, 105, 115, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 96, 226, 139, 175, 96, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,2999604245836119670 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject,17181912203459092978 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,3655157751251404823 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject,11545192291877000663 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject,17795760795678075751 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value: LeanStringObject<118> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 118, m_capacity: 118, m_length: 115, m_data: [119, 104, 101, 110, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 44, 32, 116, 104, 101, 32, 109, 97, 120, 105, 109, 117, 109, 32, 115, 105, 122, 101, 32, 111, 102, 32, 97, 32, 116, 101, 114, 109, 32, 97, 108, 108, 111, 119, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 105, 116, 32, 105, 115, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 96, 226, 139, 175, 96, 44, 32, 102, 111, 114, 32, 116, 97, 99, 116, 105, 99, 32, 103, 111, 97, 108, 115, 0]};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 255 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__value) as *mut LeanObject,8935266838699583260 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4__value) as *mut LeanObject,2999604245836119670 as *mut LeanObject] };
static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject,9023692752762089698 as *mut LeanObject] };
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__value) as *mut LeanObject,9911732233880632598 as *mut LeanObject] };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [10, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__0_value
        ) as *mut LeanObject],
    };
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_getGoalPrefix___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 138, 162, 32, 0],
};
static mut l_Lean_Meta_getGoalPrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getGoalPrefix___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_getGoalPrefix___closed__1_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [124, 32, 0],
};
static mut l_Lean_Meta_getGoalPrefix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getGoalPrefix___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value:
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
    m_data: [32, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 58, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 32, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 5,
    m_data: [32, 58, 61, 32, 226, 139, 175, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__2_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 58, 61, 0],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__4_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5_value)
        as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_ppGoal___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 97, 115, 101, 32, 0],
};
static mut l_Lean_Meta_ppGoal___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ppGoal___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Meta_ppGoal___lam__0___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Meta_ppGoal___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_ppGoal___closed__0_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [117, 110, 107, 110, 111, 119, 110, 32, 103, 111, 97, 108, 0],
};
static mut l_Lean_Meta_ppGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_ppGoal___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Meta_ppGoal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_ppGoal___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_ppGoal___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_ppGoal___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_ppGoal___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_ppGoal___closed__3_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(
    mut v_name_1180_: *mut LeanObject,
    mut v_decl_1181_: *mut LeanObject,
    mut v_ref_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u8 = 0;
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1198_: u8 = 0;
    let mut v_unused_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1203_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1184_ = lean_ctor_get(v_decl_1181_, 0);
                v_descr_1185_ = lean_ctor_get(v_decl_1181_, 1);
                v_deprecation_x3f_1186_ = lean_ctor_get(v_decl_1181_, 2);
                v___x_1187_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1188_ = (lean_unbox(v_defValue_1184_) as u8);
                lean_ctor_set_uint8(v___x_1187_, 0 as u32, v___x_1188_);
                lean_inc(v_deprecation_x3f_1186_);
                lean_inc_ref(v_descr_1185_);
                lean_inc_n(v_name_1180_, 2);
                v___x_1189_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1189_, 0, v_name_1180_);
                lean_ctor_set(v___x_1189_, 1, v_ref_1182_);
                lean_ctor_set(v___x_1189_, 2, v___x_1187_);
                lean_ctor_set(v___x_1189_, 3, v_descr_1185_);
                lean_ctor_set(v___x_1189_, 4, v_deprecation_x3f_1186_);
                v___x_1190_ = lean_register_option(v_name_1180_, v___x_1189_);
                if lean_obj_tag(v___x_1190_) == 0 {
                    v_isSharedCheck_1198_ = (!lean_is_exclusive(v___x_1190_)) as u8;
                    if v_isSharedCheck_1198_ == 0 {
                        v_unused_1199_ = lean_ctor_get(v___x_1190_, 0);
                        lean_dec(v_unused_1199_);
                        v___x_1192_ = v___x_1190_;
                        v_isShared_1193_ = v_isSharedCheck_1198_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1190_);
                        v___x_1192_ = lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1198_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1180_);
                    v_a_1200_ = lean_ctor_get(v___x_1190_, 0);
                    v_isSharedCheck_1207_ = (!lean_is_exclusive(v___x_1190_)) as u8;
                    if v_isSharedCheck_1207_ == 0 {
                        v___x_1202_ = v___x_1190_;
                        v_isShared_1203_ = v_isSharedCheck_1207_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1200_);
                        lean_dec(v___x_1190_);
                        v___x_1202_ = lean_box(0);
                        v_isShared_1203_ = v_isSharedCheck_1207_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1184_);
                v___x_1194_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1194_, 0, v_name_1180_);
                lean_ctor_set(v___x_1194_, 1, v_defValue_1184_);
                if v_isShared_1193_ == 0 {
                    lean_ctor_set(v___x_1192_, 0, v___x_1194_);
                    v___x_1196_ = v___x_1192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
                    v___x_1196_ = v_reuseFailAlloc_1197_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1196_;
            }
            3 => {
                if v_isShared_1203_ == 0 {
                    v___x_1205_ = v___x_1202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
                    v___x_1205_ = v_reuseFailAlloc_1206_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1208_: *mut LeanObject,
    mut v_decl_1209_: *mut LeanObject,
    mut v_ref_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_res_1212_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v_name_1208_, v_decl_1209_, v_ref_1210_);
    lean_dec_ref(v_decl_1209_);
    return v_res_1212_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    v___x_1232_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_;
    v___x_1233_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_;
    v___x_1234_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_;
    v___x_1235_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_1232_, v___x_1233_, v___x_1234_);
    return v___x_1235_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4____boxed(
    mut v_a_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1237_: *mut LeanObject = core::ptr::null_mut();
    v_res_1237_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
    return v_res_1237_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    v___x_1254_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_;
    v___x_1255_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_;
    v___x_1256_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_;
    v___x_1257_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_1254_, v___x_1255_, v___x_1256_);
    return v___x_1257_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4____boxed(
    mut v_a_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1259_: *mut LeanObject = core::ptr::null_mut();
    v_res_1259_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
    return v_res_1259_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_;
    v___x_1277_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_;
    v___x_1278_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_;
    v___x_1279_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_1276_, v___x_1277_, v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4____boxed(
    mut v_a_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1281_: *mut LeanObject = core::ptr::null_mut();
    v_res_1281_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
    return v_res_1281_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_;
    v___x_1299_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_;
    v___x_1300_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_;
    v___x_1301_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4__spec__0(v___x_1298_, v___x_1299_, v___x_1300_);
    return v___x_1301_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4____boxed(
    mut v_a_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1303_: *mut LeanObject = core::ptr::null_mut();
    v_res_1303_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
    return v_res_1303_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(
    mut v_name_1304_: *mut LeanObject,
    mut v_decl_1305_: *mut LeanObject,
    mut v_ref_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_unused_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1308_ = lean_ctor_get(v_decl_1305_, 0);
                v_descr_1309_ = lean_ctor_get(v_decl_1305_, 1);
                v_deprecation_x3f_1310_ = lean_ctor_get(v_decl_1305_, 2);
                lean_inc(v_defValue_1308_);
                v___x_1311_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1311_, 0, v_defValue_1308_);
                lean_inc(v_deprecation_x3f_1310_);
                lean_inc_ref(v_descr_1309_);
                lean_inc_n(v_name_1304_, 2);
                v___x_1312_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1312_, 0, v_name_1304_);
                lean_ctor_set(v___x_1312_, 1, v_ref_1306_);
                lean_ctor_set(v___x_1312_, 2, v___x_1311_);
                lean_ctor_set(v___x_1312_, 3, v_descr_1309_);
                lean_ctor_set(v___x_1312_, 4, v_deprecation_x3f_1310_);
                v___x_1313_ = lean_register_option(v_name_1304_, v___x_1312_);
                if lean_obj_tag(v___x_1313_) == 0 {
                    v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1313_)) as u8;
                    if v_isSharedCheck_1321_ == 0 {
                        v_unused_1322_ = lean_ctor_get(v___x_1313_, 0);
                        lean_dec(v_unused_1322_);
                        v___x_1315_ = v___x_1313_;
                        v_isShared_1316_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1313_);
                        v___x_1315_ = lean_box(0);
                        v_isShared_1316_ = v_isSharedCheck_1321_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1304_);
                    v_a_1323_ = lean_ctor_get(v___x_1313_, 0);
                    v_isSharedCheck_1330_ = (!lean_is_exclusive(v___x_1313_)) as u8;
                    if v_isSharedCheck_1330_ == 0 {
                        v___x_1325_ = v___x_1313_;
                        v_isShared_1326_ = v_isSharedCheck_1330_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1323_);
                        lean_dec(v___x_1313_);
                        v___x_1325_ = lean_box(0);
                        v_isShared_1326_ = v_isSharedCheck_1330_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1308_);
                v___x_1317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v_name_1304_);
                lean_ctor_set(v___x_1317_, 1, v_defValue_1308_);
                if v_isShared_1316_ == 0 {
                    lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1319_;
            }
            3 => {
                if v_isShared_1326_ == 0 {
                    v___x_1328_ = v___x_1325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_1331_: *mut LeanObject,
    mut v_decl_1332_: *mut LeanObject,
    mut v_ref_1333_: *mut LeanObject,
    mut v_a_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1335_: *mut LeanObject = core::ptr::null_mut();
    v_res_1335_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v_name_1331_, v_decl_1332_, v_ref_1333_);
    lean_dec_ref(v_decl_1332_);
    return v_res_1335_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1353_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_;
    v___x_1354_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_;
    v___x_1355_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_;
    v___x_1356_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_1353_, v___x_1354_, v___x_1355_);
    return v___x_1356_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4____boxed(
    mut v_a_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1358_: *mut LeanObject = core::ptr::null_mut();
    v_res_1358_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
    return v_res_1358_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    v___x_1378_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_;
    v___x_1379_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_;
    v___x_1380_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_;
    v___x_1381_ = l_Lean_Option_register___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4__spec__0(v___x_1378_, v___x_1379_, v___x_1380_);
    return v___x_1381_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4____boxed(
    mut v_a_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1383_: *mut LeanObject = core::ptr::null_mut();
    v_res_1383_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
    return v_res_1383_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(
    mut v_opts_1384_: *mut LeanObject,
    mut v_opt_1385_: *mut LeanObject,
) -> u8 {
    let mut v_name_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v_name_1386_ = lean_ctor_get(v_opt_1385_, 0);
    v_defValue_1387_ = lean_ctor_get(v_opt_1385_, 1);
    v_map_1388_ = lean_ctor_get(v_opts_1384_, 0);
    v___x_1389_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1388_,
            v_name_1386_,
        );
    if lean_obj_tag(v___x_1389_) == 0 {
        let mut v___x_1390_: u8 = 0;
        v___x_1390_ = (lean_unbox(v_defValue_1387_) as u8);
        return v___x_1390_;
    } else {
        let mut v_val_1391_: *mut LeanObject = core::ptr::null_mut();
        v_val_1391_ = lean_ctor_get(v___x_1389_, 0);
        lean_inc(v_val_1391_);
        lean_dec_ref_known(v___x_1389_, 1);
        if lean_obj_tag(v_val_1391_) == 1 {
            let mut v_v_1392_: u8 = 0;
            v_v_1392_ = lean_ctor_get_uint8(v_val_1391_, 0 as u32);
            lean_dec_ref_known(v_val_1391_, 0);
            return v_v_1392_;
        } else {
            let mut v___x_1393_: u8 = 0;
            lean_dec(v_val_1391_);
            v___x_1393_ = (lean_unbox(v_defValue_1387_) as u8);
            return v___x_1393_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0___boxed(
    mut v_opts_1394_: *mut LeanObject,
    mut v_opt_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: u8 = 0;
    let mut v_r_1397_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(
        v_opts_1394_,
        v_opt_1395_,
    );
    lean_dec_ref(v_opt_1395_);
    lean_dec_ref(v_opts_1394_);
    v_r_1397_ = lean_box((v_res_1396_) as usize);
    return v_r_1397_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(
    mut v_opts_1398_: *mut LeanObject,
    mut v_opt_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    v_name_1400_ = lean_ctor_get(v_opt_1399_, 0);
    v_defValue_1401_ = lean_ctor_get(v_opt_1399_, 1);
    v_map_1402_ = lean_ctor_get(v_opts_1398_, 0);
    v___x_1403_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1402_,
            v_name_1400_,
        );
    if lean_obj_tag(v___x_1403_) == 0 {
        lean_inc(v_defValue_1401_);
        return v_defValue_1401_;
    } else {
        let mut v_val_1404_: *mut LeanObject = core::ptr::null_mut();
        v_val_1404_ = lean_ctor_get(v___x_1403_, 0);
        lean_inc(v_val_1404_);
        lean_dec_ref_known(v___x_1403_, 1);
        if lean_obj_tag(v_val_1404_) == 3 {
            let mut v_v_1405_: *mut LeanObject = core::ptr::null_mut();
            v_v_1405_ = lean_ctor_get(v_val_1404_, 0);
            lean_inc(v_v_1405_);
            lean_dec_ref_known(v_val_1404_, 1);
            return v_v_1405_;
        } else {
            lean_dec(v_val_1404_);
            lean_inc(v_defValue_1401_);
            return v_defValue_1401_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1___boxed(
    mut v_opts_1406_: *mut LeanObject,
    mut v_opt_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1408_: *mut LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(
        v_opts_1406_,
        v_opt_1407_,
    );
    lean_dec_ref(v_opt_1407_);
    lean_dec_ref(v_opts_1406_);
    return v_res_1408_;
}
pub unsafe fn l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(
    mut v_tactic_1409_: u8,
    mut v_e_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u32 = 0;
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u8 = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: u8 = 0;
    let mut v_options_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1424_ = l_Lean_Expr_isAtomic(v_e_1410_);
                v___x_1425_ = 1;
                if v___x_1424_ == 0 {
                    v_options_1426_ = lean_ctor_get(v_a_1411_, 2);
                    v___x_1427_ = l_Lean_Meta_pp_showLetValues;
                    v___x_1428_ =
                        l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(
                            v_options_1426_,
                            v___x_1427_,
                        );
                    if v___x_1428_ == 0 {
                        v___x_1429_ = l_Lean_Meta_pp_showLetValues_threshold;
                        v___x_1430_ =
                            l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(
                                v_options_1426_,
                                v___x_1429_,
                            );
                        if v_tactic_1409_ == 0 {
                            v___x_1434_ = lean_unsigned_to_nat(0);
                            v___y_1432_ = v___x_1434_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1435_ = l_Lean_Meta_pp_showLetValues_tactic_threshold;
                            v___x_1436_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__1(v_options_1426_, v___x_1435_);
                            v___y_1432_ = v___x_1436_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1437_ = lean_box((v___x_1425_) as usize);
                        v___x_1438_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1438_, 0, v___x_1437_);
                        return v___x_1438_;
                    }
                } else {
                    v___x_1439_ = lean_box((v___x_1425_) as usize);
                    v___x_1440_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1440_, 0, v___x_1439_);
                    return v___x_1440_;
                }
            }
            1 => {
                v___x_1415_ = l_Lean_Expr_approxDepth(v_e_1410_);
                v___x_1416_ = lean_uint32_to_nat(v___x_1415_);
                v___x_1417_ = lean_nat_dec_le(v___x_1416_, v___y_1414_);
                lean_dec(v___y_1414_);
                lean_dec(v___x_1416_);
                v___x_1418_ = lean_box((v___x_1417_) as usize);
                v___x_1419_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1419_, 0, v___x_1418_);
                return v___x_1419_;
            }
            2 => {
                v___x_1422_ = lean_unsigned_to_nat(254);
                v___x_1423_ = lean_nat_dec_le(v___x_1422_, v___y_1421_);
                if v___x_1423_ == 0 {
                    v___y_1414_ = v___y_1421_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1421_);
                    v___y_1414_ = v___x_1422_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1433_ = lean_nat_dec_le(v___x_1430_, v___y_1432_);
                if v___x_1433_ == 0 {
                    lean_dec(v___y_1432_);
                    v___y_1421_ = v___x_1430_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_1430_);
                    v___y_1421_ = v___y_1432_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppGoal_shouldShowLetValue___redArg___boxed(
    mut v_tactic_1441_: *mut LeanObject,
    mut v_e_1442_: *mut LeanObject,
    mut v_a_1443_: *mut LeanObject,
    mut v_a_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tactic_boxed_1445_: u8 = 0;
    let mut v_res_1446_: *mut LeanObject = core::ptr::null_mut();
    v_tactic_boxed_1445_ = (lean_unbox(v_tactic_1441_) as u8);
    v_res_1446_ =
        l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_boxed_1445_, v_e_1442_, v_a_1443_);
    lean_dec_ref(v_a_1443_);
    lean_dec_ref(v_e_1442_);
    return v_res_1446_;
}
pub unsafe fn l_Lean_Meta_ppGoal_shouldShowLetValue(
    mut v_tactic_1447_: u8,
    mut v_e_1448_: *mut LeanObject,
    mut v_a_1449_: *mut LeanObject,
    mut v_a_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
    mut v_a_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ =
        l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(v_tactic_1447_, v_e_1448_, v_a_1451_);
    return v___x_1454_;
}
pub unsafe fn l_Lean_Meta_ppGoal_shouldShowLetValue___boxed(
    mut v_tactic_1455_: *mut LeanObject,
    mut v_e_1456_: *mut LeanObject,
    mut v_a_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v_a_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
    mut v_a_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tactic_boxed_1462_: u8 = 0;
    let mut v_res_1463_: *mut LeanObject = core::ptr::null_mut();
    v_tactic_boxed_1462_ = (lean_unbox(v_tactic_1455_) as u8);
    v_res_1463_ = l_Lean_Meta_ppGoal_shouldShowLetValue(
        v_tactic_boxed_1462_,
        v_e_1456_,
        v_a_1457_,
        v_a_1458_,
        v_a_1459_,
        v_a_1460_,
    );
    lean_dec(v_a_1460_);
    lean_dec_ref(v_a_1459_);
    lean_dec(v_a_1458_);
    lean_dec_ref(v_a_1457_);
    lean_dec_ref(v_e_1456_);
    return v_res_1463_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(
    mut v_fmt_1467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1468_: u8 = 0;
    v___x_1468_ = l_Std_Format_isNil(v_fmt_1467_);
    if v___x_1468_ == 0 {
        let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
        v___x_1469_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1;
        v___x_1470_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1470_, 0, v_fmt_1467_);
        lean_ctor_set(v___x_1470_, 1, v___x_1469_);
        return v___x_1470_;
    } else {
        return v_fmt_1467_;
    }
}
pub unsafe fn l_Lean_Meta_getGoalPrefix(mut v_mvarDecl_1473_: *mut LeanObject) -> *mut LeanObject {
    let mut v_type_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v_type_1474_ = lean_ctor_get(v_mvarDecl_1473_, 2);
    v___x_1475_ = l_Lean_isLHSGoal_x3f(v_type_1474_);
    if lean_obj_tag(v___x_1475_) == 0 {
        let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
        v___x_1476_ = l_Lean_Meta_getGoalPrefix___closed__0;
        return v___x_1476_;
    } else {
        let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_1475_, 1);
        v___x_1477_ = l_Lean_Meta_getGoalPrefix___closed__1;
        return v___x_1477_;
    }
}
pub unsafe fn l_Lean_Meta_getGoalPrefix___boxed(
    mut v_mvarDecl_1478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1479_: *mut LeanObject = core::ptr::null_mut();
    v_res_1479_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_1478_);
    lean_dec_ref(v_mvarDecl_1478_);
    return v_res_1479_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(
    mut v_x_1480_: *mut LeanObject,
    mut v_x_1481_: *mut LeanObject,
    mut v_x_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1482_) == 0 {
                    lean_dec(v_x_1480_);
                    return v_x_1481_;
                } else {
                    v_head_1483_ = lean_ctor_get(v_x_1482_, 0);
                    v_tail_1484_ = lean_ctor_get(v_x_1482_, 1);
                    v_isSharedCheck_1496_ = (!lean_is_exclusive(v_x_1482_)) as u8;
                    if v_isSharedCheck_1496_ == 0 {
                        v___x_1486_ = v_x_1482_;
                        v_isShared_1487_ = v_isSharedCheck_1496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1484_);
                        lean_inc(v_head_1483_);
                        lean_dec(v_x_1482_);
                        v___x_1486_ = lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1496_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1480_);
                if v_isShared_1487_ == 0 {
                    lean_ctor_set_tag(v___x_1486_, 5);
                    lean_ctor_set(v___x_1486_, 1, v_x_1480_);
                    lean_ctor_set(v___x_1486_, 0, v_x_1481_);
                    v___x_1489_ = v___x_1486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_x_1481_);
                    lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_x_1480_);
                    v___x_1489_ = v_reuseFailAlloc_1495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1490_ = 1;
                v___x_1491_ = l_Lean_Name_toString(v_head_1483_, v___x_1490_);
                v___x_1492_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1492_, 0, v___x_1491_);
                v___x_1493_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1493_, 0, v___x_1489_);
                lean_ctor_set(v___x_1493_, 1, v___x_1492_);
                v_x_1481_ = v___x_1493_;
                v_x_1482_ = v_tail_1484_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(
    mut v_x_1497_: *mut LeanObject,
    mut v_x_1498_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1497_) == 0 {
        let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1498_);
        v___x_1499_ = lean_box(0);
        return v___x_1499_;
    } else {
        let mut v_tail_1500_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1500_ = lean_ctor_get(v_x_1497_, 1);
        if lean_obj_tag(v_tail_1500_) == 0 {
            let mut v_head_1501_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1502_: u8 = 0;
            let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1498_);
            v_head_1501_ = lean_ctor_get(v_x_1497_, 0);
            lean_inc(v_head_1501_);
            lean_dec_ref_known(v_x_1497_, 2);
            v___x_1502_ = 1;
            v___x_1503_ = l_Lean_Name_toString(v_head_1501_, v___x_1502_);
            v___x_1504_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_1504_, 0, v___x_1503_);
            return v___x_1504_;
        } else {
            let mut v_head_1505_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1506_: u8 = 0;
            let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1500_);
            v_head_1505_ = lean_ctor_get(v_x_1497_, 0);
            lean_inc(v_head_1505_);
            lean_dec_ref_known(v_x_1497_, 2);
            v___x_1506_ = 1;
            v___x_1507_ = l_Lean_Name_toString(v_head_1505_, v___x_1506_);
            v___x_1508_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_1508_, 0, v___x_1507_);
            v___x_1509_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0_spec__0(v_x_1498_, v___x_1508_, v_tail_1500_);
            return v___x_1509_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
    mut v_indent_1516_: *mut LeanObject,
    mut v_ids_1517_: *mut LeanObject,
    mut v_type_x3f_1518_: *mut LeanObject,
    mut v_fmt_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
    mut v_a_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1525_: u8 = 0;
    let mut v_fmt_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1525_ = l_List_isEmpty___redArg(v_ids_1517_);
                if v___x_1525_ == 0 {
                    v_fmt_1526_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_fmt_1519_);
                    if lean_obj_tag(v_type_x3f_1518_) == 0 {
                        lean_dec(v_ids_1517_);
                        lean_dec(v_indent_1516_);
                        v___x_1527_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1527_, 0, v_fmt_1526_);
                        return v___x_1527_;
                    } else {
                        v_val_1528_ = lean_ctor_get(v_type_x3f_1518_, 0);
                        lean_inc(v_val_1528_);
                        lean_dec_ref_known(v_type_x3f_1518_, 1);
                        v___x_1529_ = l_Lean_Meta_ppExpr(
                            v_val_1528_,
                            v_a_1520_,
                            v_a_1521_,
                            v_a_1522_,
                            v_a_1523_,
                        );
                        if lean_obj_tag(v___x_1529_) == 0 {
                            v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
                            v_isSharedCheck_1549_ = (!lean_is_exclusive(v___x_1529_)) as u8;
                            if v_isSharedCheck_1549_ == 0 {
                                v___x_1532_ = v___x_1529_;
                                v_isShared_1533_ = v_isSharedCheck_1549_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1530_);
                                lean_dec(v___x_1529_);
                                v___x_1532_ = lean_box(0);
                                v_isShared_1533_ = v_isSharedCheck_1549_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fmt_1526_);
                            lean_dec(v_ids_1517_);
                            lean_dec(v_indent_1516_);
                            return v___x_1529_;
                        }
                    }
                } else {
                    lean_dec(v_type_x3f_1518_);
                    lean_dec(v_ids_1517_);
                    lean_dec(v_indent_1516_);
                    v___x_1550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1550_, 0, v_fmt_1519_);
                    return v___x_1550_;
                }
            }
            1 => {
                v___x_1534_ = l_List_reverse___redArg(v_ids_1517_);
                v___x_1535_ =
                    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__1;
                v___x_1536_ = l_Std_Format_joinSep___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending_spec__0(v___x_1534_, v___x_1535_);
                v___x_1537_ =
                    l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___closed__3;
                v___x_1538_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1538_, 0, v___x_1536_);
                lean_ctor_set(v___x_1538_, 1, v___x_1537_);
                v___x_1539_ = lean_box(1);
                v___x_1540_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1540_, 0, v___x_1539_);
                lean_ctor_set(v___x_1540_, 1, v_a_1530_);
                v___x_1541_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1541_, 0, v_indent_1516_);
                lean_ctor_set(v___x_1541_, 1, v___x_1540_);
                v___x_1542_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1542_, 0, v___x_1538_);
                lean_ctor_set(v___x_1542_, 1, v___x_1541_);
                v___x_1543_ = 0;
                v___x_1544_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1544_, 0, v___x_1542_);
                lean_ctor_set_uint8(
                    v___x_1544_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1543_,
                );
                v___x_1545_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1545_, 0, v_fmt_1526_);
                lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                if v_isShared_1533_ == 0 {
                    lean_ctor_set(v___x_1532_, 0, v___x_1545_);
                    v___x_1547_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
                    v___x_1547_ = v_reuseFailAlloc_1548_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending___boxed(
    mut v_indent_1551_: *mut LeanObject,
    mut v_ids_1552_: *mut LeanObject,
    mut v_type_x3f_1553_: *mut LeanObject,
    mut v_fmt_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
        v_indent_1551_,
        v_ids_1552_,
        v_type_x3f_1553_,
        v_fmt_1554_,
        v_a_1555_,
        v_a_1556_,
        v_a_1557_,
        v_a_1558_,
    );
    lean_dec(v_a_1558_);
    lean_dec_ref(v_a_1557_);
    lean_dec(v_a_1556_);
    lean_dec_ref(v_a_1555_);
    return v_res_1560_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(
    mut v_e_1561_: *mut LeanObject,
    mut v___y_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1578_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1584_: u8 = 0;
    let mut v_unused_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1564_ = l_Lean_Expr_hasMVar(v_e_1561_);
                if v___x_1564_ == 0 {
                    v___x_1565_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1565_, 0, v_e_1561_);
                    return v___x_1565_;
                } else {
                    v___x_1566_ = lean_st_ref_get(v___y_1562_);
                    v_mctx_1567_ = lean_ctor_get(v___x_1566_, 0);
                    lean_inc_ref(v_mctx_1567_);
                    lean_dec(v___x_1566_);
                    v___x_1568_ = l_Lean_instantiateMVarsCore(v_mctx_1567_, v_e_1561_);
                    v_fst_1569_ = lean_ctor_get(v___x_1568_, 0);
                    lean_inc(v_fst_1569_);
                    v_snd_1570_ = lean_ctor_get(v___x_1568_, 1);
                    lean_inc(v_snd_1570_);
                    lean_dec_ref(v___x_1568_);
                    v___x_1571_ = lean_st_ref_take(v___y_1562_);
                    v_cache_1572_ = lean_ctor_get(v___x_1571_, 1);
                    v_zetaDeltaFVarIds_1573_ = lean_ctor_get(v___x_1571_, 2);
                    v_postponed_1574_ = lean_ctor_get(v___x_1571_, 3);
                    v_diag_1575_ = lean_ctor_get(v___x_1571_, 4);
                    v_isSharedCheck_1584_ = (!lean_is_exclusive(v___x_1571_)) as u8;
                    if v_isSharedCheck_1584_ == 0 {
                        v_unused_1585_ = lean_ctor_get(v___x_1571_, 0);
                        lean_dec(v_unused_1585_);
                        v___x_1577_ = v___x_1571_;
                        v_isShared_1578_ = v_isSharedCheck_1584_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1575_);
                        lean_inc(v_postponed_1574_);
                        lean_inc(v_zetaDeltaFVarIds_1573_);
                        lean_inc(v_cache_1572_);
                        lean_dec(v___x_1571_);
                        v___x_1577_ = lean_box(0);
                        v_isShared_1578_ = v_isSharedCheck_1584_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1578_ == 0 {
                    lean_ctor_set(v___x_1577_, 0, v_snd_1570_);
                    v___x_1580_ = v___x_1577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_snd_1570_);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_cache_1572_);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_zetaDeltaFVarIds_1573_);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_postponed_1574_);
                    lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_diag_1575_);
                    v___x_1580_ = v_reuseFailAlloc_1583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1581_ = lean_st_ref_set(v___y_1562_, v___x_1580_);
                v___x_1582_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1582_, 0, v_fst_1569_);
                return v___x_1582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg___boxed(
    mut v_e_1586_: *mut LeanObject,
    mut v___y_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1589_: *mut LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_1586_, v___y_1587_);
    lean_dec(v___y_1587_);
    return v_res_1589_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(
    mut v_e_1590_: *mut LeanObject,
    mut v___y_1591_: *mut LeanObject,
    mut v___y_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    v___x_1596_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_e_1590_, v___y_1592_);
    return v___x_1596_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___boxed(
    mut v_e_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0(v_e_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
    lean_dec(v___y_1601_);
    lean_dec_ref(v___y_1600_);
    lean_dec(v___y_1599_);
    lean_dec_ref(v___y_1598_);
    return v_res_1603_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(
    mut v_x_1604_: *mut LeanObject,
    mut v_x_1605_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1604_) == 0 {
        if lean_obj_tag(v_x_1605_) == 0 {
            let mut v___x_1606_: u8 = 0;
            v___x_1606_ = 1;
            return v___x_1606_;
        } else {
            let mut v___x_1607_: u8 = 0;
            v___x_1607_ = 0;
            return v___x_1607_;
        }
    } else {
        if lean_obj_tag(v_x_1605_) == 0 {
            let mut v___x_1608_: u8 = 0;
            v___x_1608_ = 0;
            return v___x_1608_;
        } else {
            let mut v_val_1609_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1610_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1611_: u8 = 0;
            v_val_1609_ = lean_ctor_get(v_x_1604_, 0);
            v_val_1610_ = lean_ctor_get(v_x_1605_, 0);
            v___x_1611_ = lean_expr_eqv(v_val_1609_, v_val_1610_);
            return v___x_1611_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1___boxed(
    mut v_x_1612_: *mut LeanObject,
    mut v_x_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1614_: u8 = 0;
    let mut v_r_1615_: *mut LeanObject = core::ptr::null_mut();
    v_res_1614_ =
        l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(
            v_x_1612_, v_x_1613_,
        );
    lean_dec(v_x_1613_);
    lean_dec(v_x_1612_);
    v_r_1615_ = lean_box((v_res_1614_) as usize);
    return v_r_1615_;
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(
    mut v_indent_1625_: *mut LeanObject,
    mut v_tactic_1626_: u8,
    mut v_varNames_1627_: *mut LeanObject,
    mut v_prevType_x3f_1628_: *mut LeanObject,
    mut v_fmt_1629_: *mut LeanObject,
    mut v_localDecl_1630_: *mut LeanObject,
    mut v_a_1631_: *mut LeanObject,
    mut v_a_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userName_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1642_: u8 = 0;
    let mut v_varName_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1650_: u8 = 0;
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: u8 = 0;
    let mut v_isSharedCheck_1679_: u8 = 0;
    let mut v_nondep_1680_: u8 = 0;
    let mut v_userName_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v_varName_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fmtElem_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1735_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1739_: u8 = 0;
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_a_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_a_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_userName_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v_varName_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1768_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1782_: u8 = 0;
    let mut v_a_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1786_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_localDecl_1630_) == 0 {
                    v_userName_1636_ = lean_ctor_get(v_localDecl_1630_, 2);
                    lean_inc(v_userName_1636_);
                    v_type_1637_ = lean_ctor_get(v_localDecl_1630_, 3);
                    lean_inc_ref(v_type_1637_);
                    lean_dec_ref_known(v_localDecl_1630_, 4);
                    v___x_1638_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1637_, v_a_1632_);
                    v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
                    v_isSharedCheck_1679_ = (!lean_is_exclusive(v___x_1638_)) as u8;
                    if v_isSharedCheck_1679_ == 0 {
                        v___x_1641_ = v___x_1638_;
                        v_isShared_1642_ = v_isSharedCheck_1679_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1639_);
                        lean_dec(v___x_1638_);
                        v___x_1641_ = lean_box(0);
                        v_isShared_1642_ = v_isSharedCheck_1679_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_nondep_1680_ = lean_ctor_get_uint8(
                        v_localDecl_1630_,
                        (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    );
                    if v_nondep_1680_ == 0 {
                        v_userName_1681_ = lean_ctor_get(v_localDecl_1630_, 2);
                        lean_inc(v_userName_1681_);
                        v_type_1682_ = lean_ctor_get(v_localDecl_1630_, 3);
                        lean_inc_ref(v_type_1682_);
                        v_value_1683_ = lean_ctor_get(v_localDecl_1630_, 4);
                        lean_inc_ref(v_value_1683_);
                        lean_dec_ref_known(v_localDecl_1630_, 5);
                        lean_inc(v_indent_1625_);
                        v___x_1684_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
                            v_indent_1625_,
                            v_varNames_1627_,
                            v_prevType_x3f_1628_,
                            v_fmt_1629_,
                            v_a_1631_,
                            v_a_1632_,
                            v_a_1633_,
                            v_a_1634_,
                        );
                        if lean_obj_tag(v___x_1684_) == 0 {
                            v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
                            lean_inc(v_a_1685_);
                            lean_dec_ref_known(v___x_1684_, 1);
                            v___x_1686_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1682_, v_a_1632_);
                            v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
                            lean_inc(v_a_1687_);
                            lean_dec_ref(v___x_1686_);
                            v___x_1688_ = l_Lean_Meta_ppExpr(
                                v_a_1687_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_,
                            );
                            if lean_obj_tag(v___x_1688_) == 0 {
                                v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
                                lean_inc(v_a_1689_);
                                lean_dec_ref_known(v___x_1688_, 1);
                                v___x_1690_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_value_1683_, v_a_1632_);
                                v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
                                v_isSharedCheck_1742_ = (!lean_is_exclusive(v___x_1690_)) as u8;
                                if v_isSharedCheck_1742_ == 0 {
                                    v___x_1693_ = v___x_1690_;
                                    v_isShared_1694_ = v_isSharedCheck_1742_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_1691_);
                                    lean_dec(v___x_1690_);
                                    v___x_1693_ = lean_box(0);
                                    v_isShared_1694_ = v_isSharedCheck_1742_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_1685_);
                                lean_dec_ref(v_value_1683_);
                                lean_dec(v_userName_1681_);
                                lean_dec(v_indent_1625_);
                                v_a_1743_ = lean_ctor_get(v___x_1688_, 0);
                                v_isSharedCheck_1750_ = (!lean_is_exclusive(v___x_1688_)) as u8;
                                if v_isSharedCheck_1750_ == 0 {
                                    v___x_1745_ = v___x_1688_;
                                    v_isShared_1746_ = v_isSharedCheck_1750_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_1743_);
                                    lean_dec(v___x_1688_);
                                    v___x_1745_ = lean_box(0);
                                    v_isShared_1746_ = v_isSharedCheck_1750_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_value_1683_);
                            lean_dec_ref(v_type_1682_);
                            lean_dec(v_userName_1681_);
                            lean_dec(v_indent_1625_);
                            v_a_1751_ = lean_ctor_get(v___x_1684_, 0);
                            v_isSharedCheck_1758_ = (!lean_is_exclusive(v___x_1684_)) as u8;
                            if v_isSharedCheck_1758_ == 0 {
                                v___x_1753_ = v___x_1684_;
                                v_isShared_1754_ = v_isSharedCheck_1758_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_1751_);
                                lean_dec(v___x_1684_);
                                v___x_1753_ = lean_box(0);
                                v_isShared_1754_ = v_isSharedCheck_1758_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        v_userName_1759_ = lean_ctor_get(v_localDecl_1630_, 2);
                        lean_inc(v_userName_1759_);
                        v_type_1760_ = lean_ctor_get(v_localDecl_1630_, 3);
                        lean_inc_ref(v_type_1760_);
                        lean_dec_ref_known(v_localDecl_1630_, 5);
                        v___x_1761_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_1760_, v_a_1632_);
                        v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
                        v_isSharedCheck_1802_ = (!lean_is_exclusive(v___x_1761_)) as u8;
                        if v_isSharedCheck_1802_ == 0 {
                            v___x_1764_ = v___x_1761_;
                            v_isShared_1765_ = v_isSharedCheck_1802_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_1762_);
                            lean_dec(v___x_1761_);
                            v___x_1764_ = lean_box(0);
                            v_isShared_1765_ = v_isSharedCheck_1802_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_varName_1643_ = lean_simp_macro_scopes(v_userName_1636_);
                v___x_1675_ = lean_box(0);
                v___x_1676_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_1628_, v___x_1675_);
                if v___x_1676_ == 0 {
                    lean_inc(v_a_1639_);
                    v___x_1677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1677_, 0, v_a_1639_);
                    v___x_1678_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_1628_, v___x_1677_);
                    lean_dec_ref_known(v___x_1677_, 1);
                    v___y_1645_ = v___x_1678_;
                    state = 2;
                    continue;
                } else {
                    v___y_1645_ = v___x_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_1645_ == 0 {
                    lean_del_object(v___x_1641_);
                    v___x_1646_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
                        v_indent_1625_,
                        v_varNames_1627_,
                        v_prevType_x3f_1628_,
                        v_fmt_1629_,
                        v_a_1631_,
                        v_a_1632_,
                        v_a_1633_,
                        v_a_1634_,
                    );
                    if lean_obj_tag(v___x_1646_) == 0 {
                        v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
                        v_isSharedCheck_1659_ = (!lean_is_exclusive(v___x_1646_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v___x_1649_ = v___x_1646_;
                            v_isShared_1650_ = v_isSharedCheck_1659_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1647_);
                            lean_dec(v___x_1646_);
                            v___x_1649_ = lean_box(0);
                            v_isShared_1650_ = v_isSharedCheck_1659_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_varName_1643_);
                        lean_dec(v_a_1639_);
                        v_a_1660_ = lean_ctor_get(v___x_1646_, 0);
                        v_isSharedCheck_1667_ = (!lean_is_exclusive(v___x_1646_)) as u8;
                        if v_isSharedCheck_1667_ == 0 {
                            v___x_1662_ = v___x_1646_;
                            v_isShared_1663_ = v_isSharedCheck_1667_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1660_);
                            lean_dec(v___x_1646_);
                            v___x_1662_ = lean_box(0);
                            v_isShared_1663_ = v_isSharedCheck_1667_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_prevType_x3f_1628_);
                    lean_dec(v_indent_1625_);
                    v___x_1668_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1668_, 0, v_varName_1643_);
                    lean_ctor_set(v___x_1668_, 1, v_varNames_1627_);
                    v___x_1669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1669_, 0, v_a_1639_);
                    v___x_1670_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1670_, 0, v___x_1669_);
                    lean_ctor_set(v___x_1670_, 1, v_fmt_1629_);
                    v___x_1671_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1671_, 0, v___x_1668_);
                    lean_ctor_set(v___x_1671_, 1, v___x_1670_);
                    if v_isShared_1642_ == 0 {
                        lean_ctor_set(v___x_1641_, 0, v___x_1671_);
                        v___x_1673_ = v___x_1641_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
                        v___x_1673_ = v_reuseFailAlloc_1674_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1651_ = lean_box(0);
                v___x_1652_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1652_, 0, v_varName_1643_);
                lean_ctor_set(v___x_1652_, 1, v___x_1651_);
                v___x_1653_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1653_, 0, v_a_1639_);
                v___x_1654_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1654_, 0, v___x_1653_);
                lean_ctor_set(v___x_1654_, 1, v_a_1647_);
                v___x_1655_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1655_, 0, v___x_1652_);
                lean_ctor_set(v___x_1655_, 1, v___x_1654_);
                if v_isShared_1650_ == 0 {
                    lean_ctor_set(v___x_1649_, 0, v___x_1655_);
                    v___x_1657_ = v___x_1649_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1655_);
                    v___x_1657_ = v_reuseFailAlloc_1658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1657_;
            }
            5 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1665_;
            }
            7 => {
                return v___x_1673_;
            }
            8 => {
                v___x_1695_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(
                    v_tactic_1626_,
                    v_a_1691_,
                    v_a_1633_,
                );
                v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
                v_isSharedCheck_1741_ = (!lean_is_exclusive(v___x_1695_)) as u8;
                if v_isSharedCheck_1741_ == 0 {
                    v___x_1698_ = v___x_1695_;
                    v_isShared_1699_ = v_isSharedCheck_1741_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_1696_);
                    lean_dec(v___x_1695_);
                    v___x_1698_ = lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1741_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_varName_1700_ = lean_simp_macro_scopes(v_userName_1681_);
                v___x_1701_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_1685_);
                v___x_1714_ = 1;
                v___x_1715_ = l_Lean_Name_toString(v_varName_1700_, v___x_1714_);
                if v_isShared_1694_ == 0 {
                    lean_ctor_set_tag(v___x_1693_, 3);
                    lean_ctor_set(v___x_1693_, 0, v___x_1715_);
                    v___x_1717_ = v___x_1693_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1715_);
                    v___x_1717_ = v_reuseFailAlloc_1740_;
                    state = 12;
                    continue;
                }
            }
            10 => {
                v___x_1704_ = 0;
                v___x_1705_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1705_, 0, v_fmtElem_1703_);
                lean_ctor_set_uint8(
                    v___x_1705_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1704_,
                );
                v___x_1706_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1706_, 0, v___x_1701_);
                lean_ctor_set(v___x_1706_, 1, v___x_1705_);
                v___x_1707_ = lean_box(0);
                v___x_1708_ = lean_box(0);
                v___x_1709_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1709_, 0, v___x_1708_);
                lean_ctor_set(v___x_1709_, 1, v___x_1706_);
                v___x_1710_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1710_, 0, v___x_1707_);
                lean_ctor_set(v___x_1710_, 1, v___x_1709_);
                if v_isShared_1699_ == 0 {
                    lean_ctor_set(v___x_1698_, 0, v___x_1710_);
                    v___x_1712_ = v___x_1698_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
                    v___x_1712_ = v_reuseFailAlloc_1713_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1712_;
            }
            12 => {
                v___x_1718_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__1;
                v___x_1719_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1719_, 0, v___x_1717_);
                lean_ctor_set(v___x_1719_, 1, v___x_1718_);
                v___x_1720_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1720_, 0, v___x_1719_);
                lean_ctor_set(v___x_1720_, 1, v_a_1689_);
                v___x_1721_ = (lean_unbox(v_a_1696_) as u8);
                lean_dec(v_a_1696_);
                if v___x_1721_ == 0 {
                    lean_dec(v_a_1691_);
                    lean_dec(v_indent_1625_);
                    v___x_1722_ =
                        l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__3;
                    v___x_1723_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_1723_, 0, v___x_1720_);
                    lean_ctor_set(v___x_1723_, 1, v___x_1722_);
                    v_fmtElem_1703_ = v___x_1723_;
                    state = 10;
                    continue;
                } else {
                    v___x_1724_ =
                        l_Lean_Meta_ppExpr(v_a_1691_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
                    if lean_obj_tag(v___x_1724_) == 0 {
                        v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
                        lean_inc(v_a_1725_);
                        lean_dec_ref_known(v___x_1724_, 1);
                        v___x_1726_ =
                            l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___closed__5;
                        v___x_1727_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1727_, 0, v___x_1720_);
                        lean_ctor_set(v___x_1727_, 1, v___x_1726_);
                        v___x_1728_ = lean_box(1);
                        v___x_1729_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                        lean_ctor_set(v___x_1729_, 1, v_a_1725_);
                        v___x_1730_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v___x_1730_, 0, v_indent_1625_);
                        lean_ctor_set(v___x_1730_, 1, v___x_1729_);
                        v___x_1731_ = lean_alloc_ctor(5, 2, (0) as u32);
                        lean_ctor_set(v___x_1731_, 0, v___x_1727_);
                        lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                        v_fmtElem_1703_ = v___x_1731_;
                        state = 10;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_1720_, 2);
                        lean_dec(v___x_1701_);
                        lean_del_object(v___x_1698_);
                        lean_dec(v_indent_1625_);
                        v_a_1732_ = lean_ctor_get(v___x_1724_, 0);
                        v_isSharedCheck_1739_ = (!lean_is_exclusive(v___x_1724_)) as u8;
                        if v_isSharedCheck_1739_ == 0 {
                            v___x_1734_ = v___x_1724_;
                            v_isShared_1735_ = v_isSharedCheck_1739_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_1732_);
                            lean_dec(v___x_1724_);
                            v___x_1734_ = lean_box(0);
                            v_isShared_1735_ = v_isSharedCheck_1739_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_1735_ == 0 {
                    v___x_1737_ = v___x_1734_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
                    v___x_1737_ = v_reuseFailAlloc_1738_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1737_;
            }
            15 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1748_;
            }
            17 => {
                if v_isShared_1754_ == 0 {
                    v___x_1756_ = v___x_1753_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
                    v___x_1756_ = v_reuseFailAlloc_1757_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1756_;
            }
            19 => {
                v_varName_1766_ = lean_simp_macro_scopes(v_userName_1759_);
                v___x_1798_ = lean_box(0);
                v___x_1799_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_1628_, v___x_1798_);
                if v___x_1799_ == 0 {
                    lean_inc(v_a_1762_);
                    v___x_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1800_, 0, v_a_1762_);
                    v___x_1801_ = l_Option_instBEq_beq___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__1(v_prevType_x3f_1628_, v___x_1800_);
                    lean_dec_ref_known(v___x_1800_, 1);
                    v___y_1768_ = v___x_1801_;
                    state = 20;
                    continue;
                } else {
                    v___y_1768_ = v___x_1799_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v___y_1768_ == 0 {
                    lean_del_object(v___x_1764_);
                    v___x_1769_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
                        v_indent_1625_,
                        v_varNames_1627_,
                        v_prevType_x3f_1628_,
                        v_fmt_1629_,
                        v_a_1631_,
                        v_a_1632_,
                        v_a_1633_,
                        v_a_1634_,
                    );
                    if lean_obj_tag(v___x_1769_) == 0 {
                        v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
                        v_isSharedCheck_1782_ = (!lean_is_exclusive(v___x_1769_)) as u8;
                        if v_isSharedCheck_1782_ == 0 {
                            v___x_1772_ = v___x_1769_;
                            v_isShared_1773_ = v_isSharedCheck_1782_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_1770_);
                            lean_dec(v___x_1769_);
                            v___x_1772_ = lean_box(0);
                            v_isShared_1773_ = v_isSharedCheck_1782_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec(v_varName_1766_);
                        lean_dec(v_a_1762_);
                        v_a_1783_ = lean_ctor_get(v___x_1769_, 0);
                        v_isSharedCheck_1790_ = (!lean_is_exclusive(v___x_1769_)) as u8;
                        if v_isSharedCheck_1790_ == 0 {
                            v___x_1785_ = v___x_1769_;
                            v_isShared_1786_ = v_isSharedCheck_1790_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_1783_);
                            lean_dec(v___x_1769_);
                            v___x_1785_ = lean_box(0);
                            v_isShared_1786_ = v_isSharedCheck_1790_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_prevType_x3f_1628_);
                    lean_dec(v_indent_1625_);
                    v___x_1791_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1791_, 0, v_varName_1766_);
                    lean_ctor_set(v___x_1791_, 1, v_varNames_1627_);
                    v___x_1792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1792_, 0, v_a_1762_);
                    v___x_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                    lean_ctor_set(v___x_1793_, 1, v_fmt_1629_);
                    v___x_1794_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1794_, 0, v___x_1791_);
                    lean_ctor_set(v___x_1794_, 1, v___x_1793_);
                    if v_isShared_1765_ == 0 {
                        lean_ctor_set(v___x_1764_, 0, v___x_1794_);
                        v___x_1796_ = v___x_1764_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
                        v___x_1796_ = v_reuseFailAlloc_1797_;
                        state = 25;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1774_ = lean_box(0);
                v___x_1775_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1775_, 0, v_varName_1766_);
                lean_ctor_set(v___x_1775_, 1, v___x_1774_);
                v___x_1776_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1776_, 0, v_a_1762_);
                v___x_1777_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1777_, 0, v___x_1776_);
                lean_ctor_set(v___x_1777_, 1, v_a_1770_);
                v___x_1778_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1778_, 0, v___x_1775_);
                lean_ctor_set(v___x_1778_, 1, v___x_1777_);
                if v_isShared_1773_ == 0 {
                    lean_ctor_set(v___x_1772_, 0, v___x_1778_);
                    v___x_1780_ = v___x_1772_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1778_);
                    v___x_1780_ = v_reuseFailAlloc_1781_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1780_;
            }
            23 => {
                if v_isShared_1786_ == 0 {
                    v___x_1788_ = v___x_1785_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1788_;
            }
            25 => {
                return v___x_1796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars___boxed(
    mut v_indent_1803_: *mut LeanObject,
    mut v_tactic_1804_: *mut LeanObject,
    mut v_varNames_1805_: *mut LeanObject,
    mut v_prevType_x3f_1806_: *mut LeanObject,
    mut v_fmt_1807_: *mut LeanObject,
    mut v_localDecl_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tactic_boxed_1814_: u8 = 0;
    let mut v_res_1815_: *mut LeanObject = core::ptr::null_mut();
    v_tactic_boxed_1814_ = (lean_unbox(v_tactic_1804_) as u8);
    v_res_1815_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(
        v_indent_1803_,
        v_tactic_boxed_1814_,
        v_varNames_1805_,
        v_prevType_x3f_1806_,
        v_fmt_1807_,
        v_localDecl_1808_,
        v_a_1809_,
        v_a_1810_,
        v_a_1811_,
        v_a_1812_,
    );
    lean_dec(v_a_1812_);
    lean_dec_ref(v_a_1811_);
    lean_dec(v_a_1810_);
    lean_dec_ref(v_a_1809_);
    return v_res_1815_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(
    mut v_lctx_1816_: *mut LeanObject,
    mut v_localInsts_1817_: *mut LeanObject,
    mut v_x_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1828_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1832_: u8 = 0;
    let mut v_a_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1836_: u8 = 0;
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    lean_box(0),
                    v_lctx_1816_,
                    v_localInsts_1817_,
                    v_x_1818_,
                    v___y_1819_,
                    v___y_1820_,
                    v___y_1821_,
                    v___y_1822_,
                );
                if lean_obj_tag(v___x_1824_) == 0 {
                    v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
                    v_isSharedCheck_1832_ = (!lean_is_exclusive(v___x_1824_)) as u8;
                    if v_isSharedCheck_1832_ == 0 {
                        v___x_1827_ = v___x_1824_;
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1825_);
                        lean_dec(v___x_1824_);
                        v___x_1827_ = lean_box(0);
                        v_isShared_1828_ = v_isSharedCheck_1832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1833_ = lean_ctor_get(v___x_1824_, 0);
                    v_isSharedCheck_1840_ = (!lean_is_exclusive(v___x_1824_)) as u8;
                    if v_isSharedCheck_1840_ == 0 {
                        v___x_1835_ = v___x_1824_;
                        v_isShared_1836_ = v_isSharedCheck_1840_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1833_);
                        lean_dec(v___x_1824_);
                        v___x_1835_ = lean_box(0);
                        v_isShared_1836_ = v_isSharedCheck_1840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1828_ == 0 {
                    v___x_1830_ = v___x_1827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
                    v___x_1830_ = v_reuseFailAlloc_1831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1830_;
            }
            3 => {
                if v_isShared_1836_ == 0 {
                    v___x_1838_ = v___x_1835_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
                    v___x_1838_ = v_reuseFailAlloc_1839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg___boxed(
    mut v_lctx_1841_: *mut LeanObject,
    mut v_localInsts_1842_: *mut LeanObject,
    mut v_x_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1849_: *mut LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(
        v_lctx_1841_,
        v_localInsts_1842_,
        v_x_1843_,
        v___y_1844_,
        v___y_1845_,
        v___y_1846_,
        v___y_1847_,
    );
    lean_dec(v___y_1847_);
    lean_dec_ref(v___y_1846_);
    lean_dec(v___y_1845_);
    lean_dec_ref(v___y_1844_);
    return v_res_1849_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(
    mut v_00_u03b1_1850_: *mut LeanObject,
    mut v_lctx_1851_: *mut LeanObject,
    mut v_localInsts_1852_: *mut LeanObject,
    mut v_x_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(
        v_lctx_1851_,
        v_localInsts_1852_,
        v_x_1853_,
        v___y_1854_,
        v___y_1855_,
        v___y_1856_,
        v___y_1857_,
    );
    return v___x_1859_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___boxed(
    mut v_00_u03b1_1860_: *mut LeanObject,
    mut v_lctx_1861_: *mut LeanObject,
    mut v_localInsts_1862_: *mut LeanObject,
    mut v_x_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1(
        v_00_u03b1_1860_,
        v_lctx_1861_,
        v_localInsts_1862_,
        v_x_1863_,
        v___y_1864_,
        v___y_1865_,
        v___y_1866_,
        v___y_1867_,
    );
    lean_dec(v___y_1867_);
    lean_dec_ref(v___y_1866_);
    lean_dec(v___y_1865_);
    lean_dec_ref(v___y_1864_);
    return v_res_1869_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_unsigned_to_nat(2);
    v___x_1871_ = lean_nat_to_int(v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(
    mut v___x_1872_: u8,
    mut v___x_1873_: u8,
    mut v___x_1874_: u8,
    mut v_as_1875_: *mut LeanObject,
    mut v_i_1876_: usize,
    mut v_stop_1877_: usize,
    mut v_b_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: usize = 0;
    let mut v___x_1887_: usize = 0;
    let mut v___y_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1892_ = lean_usize_dec_eq(v_i_1876_, v_stop_1877_);
                if v___x_1892_ == 0 {
                    v___x_1893_ = lean_array_uget_borrowed(v_as_1875_, v_i_1876_);
                    if lean_obj_tag(v___x_1893_) == 0 {
                        v_a_1885_ = v_b_1878_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_1894_ = lean_ctor_get(v_b_1878_, 1);
                        v_val_1895_ = lean_ctor_get(v___x_1893_, 0);
                        v_fst_1896_ = lean_ctor_get(v_b_1878_, 0);
                        v_fst_1897_ = lean_ctor_get(v_snd_1894_, 0);
                        v_snd_1898_ = lean_ctor_get(v_snd_1894_, 1);
                        v___x_1899_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
                        if v___x_1874_ == 0 {
                            v___x_1904_ = l_Lean_LocalDecl_isAuxDecl(v_val_1895_);
                            if v___x_1904_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                v_a_1885_ = v_b_1878_;
                                state = 1;
                                continue;
                            }
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_1905_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1905_, 0, v_b_1878_);
                    return v___x_1905_;
                }
            }
            1 => {
                v___x_1886_ = 1usize;
                v___x_1887_ = lean_usize_add(v_i_1876_, v___x_1886_);
                v_i_1876_ = v___x_1887_;
                v_b_1878_ = v_a_1885_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_1890_) == 0 {
                    v_a_1891_ = lean_ctor_get(v___y_1890_, 0);
                    lean_inc(v_a_1891_);
                    lean_dec_ref_known(v___y_1890_, 1);
                    v_a_1885_ = v_a_1891_;
                    state = 1;
                    continue;
                } else {
                    return v___y_1890_;
                }
            }
            3 => {
                if v___x_1872_ == 0 {
                    v___x_1901_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1895_);
                    if v___x_1901_ == 0 {
                        lean_inc(v_snd_1898_);
                        lean_inc(v_fst_1897_);
                        lean_inc(v_fst_1896_);
                        lean_dec_ref(v_b_1878_);
                        lean_inc(v_val_1895_);
                        v___x_1902_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(
                            v___x_1899_,
                            v___x_1873_,
                            v_fst_1896_,
                            v_fst_1897_,
                            v_snd_1898_,
                            v_val_1895_,
                            v___y_1879_,
                            v___y_1880_,
                            v___y_1881_,
                            v___y_1882_,
                        );
                        v___y_1890_ = v___x_1902_;
                        state = 2;
                        continue;
                    } else {
                        v_a_1885_ = v_b_1878_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_inc(v_snd_1898_);
                    lean_inc(v_fst_1897_);
                    lean_inc(v_fst_1896_);
                    lean_dec_ref(v_b_1878_);
                    lean_inc(v_val_1895_);
                    v___x_1903_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars(
                        v___x_1899_,
                        v___x_1873_,
                        v_fst_1896_,
                        v_fst_1897_,
                        v_snd_1898_,
                        v_val_1895_,
                        v___y_1879_,
                        v___y_1880_,
                        v___y_1881_,
                        v___y_1882_,
                    );
                    v___y_1890_ = v___x_1903_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___boxed(
    mut v___x_1906_: *mut LeanObject,
    mut v___x_1907_: *mut LeanObject,
    mut v___x_1908_: *mut LeanObject,
    mut v_as_1909_: *mut LeanObject,
    mut v_i_1910_: *mut LeanObject,
    mut v_stop_1911_: *mut LeanObject,
    mut v_b_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4928__boxed_1918_: u8 = 0;
    let mut v___x_4929__boxed_1919_: u8 = 0;
    let mut v___x_4930__boxed_1920_: u8 = 0;
    let mut v_i_boxed_1921_: usize = 0;
    let mut v_stop_boxed_1922_: usize = 0;
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v___x_4928__boxed_1918_ = (lean_unbox(v___x_1906_) as u8);
    v___x_4929__boxed_1919_ = (lean_unbox(v___x_1907_) as u8);
    v___x_4930__boxed_1920_ = (lean_unbox(v___x_1908_) as u8);
    v_i_boxed_1921_ = lean_unbox_usize(v_i_1910_);
    lean_dec(v_i_1910_);
    v_stop_boxed_1922_ = lean_unbox_usize(v_stop_1911_);
    lean_dec(v_stop_1911_);
    v_res_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_4928__boxed_1918_, v___x_4929__boxed_1919_, v___x_4930__boxed_1920_, v_as_1909_, v_i_boxed_1921_, v_stop_boxed_1922_, v_b_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
    lean_dec(v___y_1916_);
    lean_dec_ref(v___y_1915_);
    lean_dec(v___y_1914_);
    lean_dec_ref(v___y_1913_);
    lean_dec_ref(v_as_1909_);
    return v_res_1923_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(
    mut v___x_1924_: u8,
    mut v___x_1925_: u8,
    mut v___x_1926_: u8,
    mut v_x_1927_: *mut LeanObject,
    mut v_x_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: usize = 0;
    let mut v___x_1949_: usize = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v_vs_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1958_: u8 = 0;
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1927_) == 0 {
                    v_cs_1934_ = lean_ctor_get(v_x_1927_, 0);
                    v_isSharedCheck_1954_ = (!lean_is_exclusive(v_x_1927_)) as u8;
                    if v_isSharedCheck_1954_ == 0 {
                        v___x_1936_ = v_x_1927_;
                        v_isShared_1937_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_1934_);
                        lean_dec(v_x_1927_);
                        v___x_1936_ = lean_box(0);
                        v_isShared_1937_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1955_ = lean_ctor_get(v_x_1927_, 0);
                    v_isSharedCheck_1975_ = (!lean_is_exclusive(v_x_1927_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1957_ = v_x_1927_;
                        v_isShared_1958_ = v_isSharedCheck_1975_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_1955_);
                        lean_dec(v_x_1927_);
                        v___x_1957_ = lean_box(0);
                        v_isShared_1958_ = v_isSharedCheck_1975_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1938_ = lean_unsigned_to_nat(0);
                v___x_1939_ = lean_array_get_size(v_cs_1934_);
                v___x_1940_ = lean_nat_dec_lt(v___x_1938_, v___x_1939_);
                if v___x_1940_ == 0 {
                    lean_dec_ref(v_cs_1934_);
                    if v_isShared_1937_ == 0 {
                        lean_ctor_set(v___x_1936_, 0, v_x_1928_);
                        v___x_1942_ = v___x_1936_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_x_1928_);
                        v___x_1942_ = v_reuseFailAlloc_1943_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1944_ = lean_nat_dec_le(v___x_1939_, v___x_1939_);
                    if v___x_1944_ == 0 {
                        if v___x_1940_ == 0 {
                            lean_dec_ref(v_cs_1934_);
                            if v_isShared_1937_ == 0 {
                                lean_ctor_set(v___x_1936_, 0, v_x_1928_);
                                v___x_1946_ = v___x_1936_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_x_1928_);
                                v___x_1946_ = v_reuseFailAlloc_1947_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1936_);
                            v___x_1948_ = 0usize;
                            v___x_1949_ = lean_usize_of_nat(v___x_1939_);
                            v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_1924_, v___x_1925_, v___x_1926_, v_cs_1934_, v___x_1948_, v___x_1949_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
                            lean_dec_ref(v_cs_1934_);
                            return v___x_1950_;
                        }
                    } else {
                        lean_del_object(v___x_1936_);
                        v___x_1951_ = 0usize;
                        v___x_1952_ = lean_usize_of_nat(v___x_1939_);
                        v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_1924_, v___x_1925_, v___x_1926_, v_cs_1934_, v___x_1951_, v___x_1952_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
                        lean_dec_ref(v_cs_1934_);
                        return v___x_1953_;
                    }
                }
            }
            2 => {
                return v___x_1942_;
            }
            3 => {
                return v___x_1946_;
            }
            4 => {
                v___x_1959_ = lean_unsigned_to_nat(0);
                v___x_1960_ = lean_array_get_size(v_vs_1955_);
                v___x_1961_ = lean_nat_dec_lt(v___x_1959_, v___x_1960_);
                if v___x_1961_ == 0 {
                    lean_dec_ref(v_vs_1955_);
                    if v_isShared_1958_ == 0 {
                        lean_ctor_set_tag(v___x_1957_, 0);
                        lean_ctor_set(v___x_1957_, 0, v_x_1928_);
                        v___x_1963_ = v___x_1957_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_x_1928_);
                        v___x_1963_ = v_reuseFailAlloc_1964_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_1965_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
                    if v___x_1965_ == 0 {
                        if v___x_1961_ == 0 {
                            lean_dec_ref(v_vs_1955_);
                            if v_isShared_1958_ == 0 {
                                lean_ctor_set_tag(v___x_1957_, 0);
                                lean_ctor_set(v___x_1957_, 0, v_x_1928_);
                                v___x_1967_ = v___x_1957_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_x_1928_);
                                v___x_1967_ = v_reuseFailAlloc_1968_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1957_);
                            v___x_1969_ = 0usize;
                            v___x_1970_ = lean_usize_of_nat(v___x_1960_);
                            v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_1924_, v___x_1925_, v___x_1926_, v_vs_1955_, v___x_1969_, v___x_1970_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
                            lean_dec_ref(v_vs_1955_);
                            return v___x_1971_;
                        }
                    } else {
                        lean_del_object(v___x_1957_);
                        v___x_1972_ = 0usize;
                        v___x_1973_ = lean_usize_of_nat(v___x_1960_);
                        v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_1924_, v___x_1925_, v___x_1926_, v_vs_1955_, v___x_1972_, v___x_1973_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
                        lean_dec_ref(v_vs_1955_);
                        return v___x_1974_;
                    }
                }
            }
            5 => {
                return v___x_1963_;
            }
            6 => {
                return v___x_1967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(
    mut v___x_1976_: u8,
    mut v___x_1977_: u8,
    mut v___x_1978_: u8,
    mut v_as_1979_: *mut LeanObject,
    mut v_i_1980_: usize,
    mut v_stop_1981_: usize,
    mut v_b_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: usize = 0;
    let mut v___x_1993_: usize = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1988_ = lean_usize_dec_eq(v_i_1980_, v_stop_1981_);
                if v___x_1988_ == 0 {
                    v___x_1989_ = lean_array_uget_borrowed(v_as_1979_, v_i_1980_);
                    lean_inc(v___x_1989_);
                    v___x_1990_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_1976_, v___x_1977_, v___x_1978_, v___x_1989_, v_b_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
                    if lean_obj_tag(v___x_1990_) == 0 {
                        v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
                        lean_inc(v_a_1991_);
                        lean_dec_ref_known(v___x_1990_, 1);
                        v___x_1992_ = 1usize;
                        v___x_1993_ = lean_usize_add(v_i_1980_, v___x_1992_);
                        v_i_1980_ = v___x_1993_;
                        v_b_1982_ = v_a_1991_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1990_;
                    }
                } else {
                    v___x_1995_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1995_, 0, v_b_1982_);
                    return v___x_1995_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v___x_1996_: *mut LeanObject,
    mut v___x_1997_: *mut LeanObject,
    mut v___x_1998_: *mut LeanObject,
    mut v_as_1999_: *mut LeanObject,
    mut v_i_2000_: *mut LeanObject,
    mut v_stop_2001_: *mut LeanObject,
    mut v_b_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4999__boxed_2008_: u8 = 0;
    let mut v___x_5000__boxed_2009_: u8 = 0;
    let mut v___x_5001__boxed_2010_: u8 = 0;
    let mut v_i_boxed_2011_: usize = 0;
    let mut v_stop_boxed_2012_: usize = 0;
    let mut v_res_2013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4999__boxed_2008_ = (lean_unbox(v___x_1996_) as u8);
    v___x_5000__boxed_2009_ = (lean_unbox(v___x_1997_) as u8);
    v___x_5001__boxed_2010_ = (lean_unbox(v___x_1998_) as u8);
    v_i_boxed_2011_ = lean_unbox_usize(v_i_2000_);
    lean_dec(v_i_2000_);
    v_stop_boxed_2012_ = lean_unbox_usize(v_stop_2001_);
    lean_dec(v_stop_2001_);
    v_res_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_4999__boxed_2008_, v___x_5000__boxed_2009_, v___x_5001__boxed_2010_, v_as_1999_, v_i_boxed_2011_, v_stop_boxed_2012_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
    lean_dec(v___y_2006_);
    lean_dec_ref(v___y_2005_);
    lean_dec(v___y_2004_);
    lean_dec_ref(v___y_2003_);
    lean_dec_ref(v_as_1999_);
    return v_res_2013_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4___boxed(
    mut v___x_2014_: *mut LeanObject,
    mut v___x_2015_: *mut LeanObject,
    mut v___x_2016_: *mut LeanObject,
    mut v_x_2017_: *mut LeanObject,
    mut v_x_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
    mut v___y_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5016__boxed_2024_: u8 = 0;
    let mut v___x_5017__boxed_2025_: u8 = 0;
    let mut v___x_5018__boxed_2026_: u8 = 0;
    let mut v_res_2027_: *mut LeanObject = core::ptr::null_mut();
    v___x_5016__boxed_2024_ = (lean_unbox(v___x_2014_) as u8);
    v___x_5017__boxed_2025_ = (lean_unbox(v___x_2015_) as u8);
    v___x_5018__boxed_2026_ = (lean_unbox(v___x_2016_) as u8);
    v_res_2027_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_5016__boxed_2024_, v___x_5017__boxed_2025_, v___x_5018__boxed_2026_, v_x_2017_, v_x_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
    lean_dec(v___y_2022_);
    lean_dec_ref(v___y_2021_);
    lean_dec(v___y_2020_);
    lean_dec_ref(v___y_2019_);
    return v_res_2027_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_2028_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(
    mut v___x_2029_: u8,
    mut v___x_2030_: u8,
    mut v___x_2031_: u8,
    mut v_x_2032_: *mut LeanObject,
    mut v_x_2033_: usize,
    mut v_x_2034_: usize,
    mut v_x_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
    mut v___y_2038_: *mut LeanObject,
    mut v___y_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: usize = 0;
    let mut v_j_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v___x_2050_: usize = 0;
    let mut v___x_2051_: usize = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: usize = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: usize = 0;
    let mut v___x_2080_: usize = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2032_) == 0 {
                    v_cs_2041_ = lean_ctor_get(v_x_2032_, 0);
                    lean_inc_ref(v_cs_2041_);
                    lean_dec_ref_known(v_x_2032_, 1);
                    v___x_2042_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___closed__0);
                    v___x_2043_ = lean_usize_shift_right(v_x_2033_, v_x_2034_);
                    v_j_2044_ = lean_usize_to_nat(v___x_2043_);
                    v___x_2045_ = lean_array_get_borrowed(v___x_2042_, v_cs_2041_, v_j_2044_);
                    v___x_2046_ = 1usize;
                    v___x_2047_ = lean_usize_shift_left(v___x_2046_, v_x_2034_);
                    v___x_2048_ = lean_usize_sub(v___x_2047_, v___x_2046_);
                    v___x_2049_ = lean_usize_land(v_x_2033_, v___x_2048_);
                    v___x_2050_ = 5usize;
                    v___x_2051_ = lean_usize_sub(v_x_2034_, v___x_2050_);
                    lean_inc(v___x_2045_);
                    v___x_2052_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_2029_, v___x_2030_, v___x_2031_, v___x_2045_, v___x_2049_, v___x_2051_, v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
                    if lean_obj_tag(v___x_2052_) == 0 {
                        v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
                        lean_inc(v_a_2053_);
                        v___x_2054_ = lean_unsigned_to_nat(1);
                        v___x_2055_ = lean_nat_add(v_j_2044_, v___x_2054_);
                        lean_dec(v_j_2044_);
                        v___x_2056_ = lean_array_get_size(v_cs_2041_);
                        v___x_2057_ = lean_nat_dec_lt(v___x_2055_, v___x_2056_);
                        if v___x_2057_ == 0 {
                            lean_dec(v___x_2055_);
                            lean_dec(v_a_2053_);
                            lean_dec_ref(v_cs_2041_);
                            return v___x_2052_;
                        } else {
                            v___x_2058_ = lean_nat_dec_le(v___x_2056_, v___x_2056_);
                            if v___x_2058_ == 0 {
                                if v___x_2057_ == 0 {
                                    lean_dec(v___x_2055_);
                                    lean_dec(v_a_2053_);
                                    lean_dec_ref(v_cs_2041_);
                                    return v___x_2052_;
                                } else {
                                    lean_dec_ref_known(v___x_2052_, 1);
                                    v___x_2059_ = lean_usize_of_nat(v___x_2055_);
                                    lean_dec(v___x_2055_);
                                    v___x_2060_ = lean_usize_of_nat(v___x_2056_);
                                    v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_2029_, v___x_2030_, v___x_2031_, v_cs_2041_, v___x_2059_, v___x_2060_, v_a_2053_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
                                    lean_dec_ref(v_cs_2041_);
                                    return v___x_2061_;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2052_, 1);
                                v___x_2062_ = lean_usize_of_nat(v___x_2055_);
                                lean_dec(v___x_2055_);
                                v___x_2063_ = lean_usize_of_nat(v___x_2056_);
                                v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2_spec__3(v___x_2029_, v___x_2030_, v___x_2031_, v_cs_2041_, v___x_2062_, v___x_2063_, v_a_2053_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
                                lean_dec_ref(v_cs_2041_);
                                return v___x_2064_;
                            }
                        }
                    } else {
                        lean_dec(v_j_2044_);
                        lean_dec_ref(v_cs_2041_);
                        return v___x_2052_;
                    }
                } else {
                    v_vs_2065_ = lean_ctor_get(v_x_2032_, 0);
                    v_isSharedCheck_2085_ = (!lean_is_exclusive(v_x_2032_)) as u8;
                    if v_isSharedCheck_2085_ == 0 {
                        v___x_2067_ = v_x_2032_;
                        v_isShared_2068_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vs_2065_);
                        lean_dec(v_x_2032_);
                        v___x_2067_ = lean_box(0);
                        v_isShared_2068_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2069_ = lean_usize_to_nat(v_x_2033_);
                v___x_2070_ = lean_array_get_size(v_vs_2065_);
                v___x_2071_ = lean_nat_dec_lt(v___x_2069_, v___x_2070_);
                if v___x_2071_ == 0 {
                    lean_dec(v___x_2069_);
                    lean_dec_ref(v_vs_2065_);
                    if v_isShared_2068_ == 0 {
                        lean_ctor_set_tag(v___x_2067_, 0);
                        lean_ctor_set(v___x_2067_, 0, v_x_2035_);
                        v___x_2073_ = v___x_2067_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_x_2035_);
                        v___x_2073_ = v_reuseFailAlloc_2074_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2075_ = lean_nat_dec_le(v___x_2070_, v___x_2070_);
                    if v___x_2075_ == 0 {
                        if v___x_2071_ == 0 {
                            lean_dec(v___x_2069_);
                            lean_dec_ref(v_vs_2065_);
                            if v_isShared_2068_ == 0 {
                                lean_ctor_set_tag(v___x_2067_, 0);
                                lean_ctor_set(v___x_2067_, 0, v_x_2035_);
                                v___x_2077_ = v___x_2067_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_x_2035_);
                                v___x_2077_ = v_reuseFailAlloc_2078_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2067_);
                            v___x_2079_ = lean_usize_of_nat(v___x_2069_);
                            lean_dec(v___x_2069_);
                            v___x_2080_ = lean_usize_of_nat(v___x_2070_);
                            v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2029_, v___x_2030_, v___x_2031_, v_vs_2065_, v___x_2079_, v___x_2080_, v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
                            lean_dec_ref(v_vs_2065_);
                            return v___x_2081_;
                        }
                    } else {
                        lean_del_object(v___x_2067_);
                        v___x_2082_ = lean_usize_of_nat(v___x_2069_);
                        lean_dec(v___x_2069_);
                        v___x_2083_ = lean_usize_of_nat(v___x_2070_);
                        v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2029_, v___x_2030_, v___x_2031_, v_vs_2065_, v___x_2082_, v___x_2083_, v_x_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
                        lean_dec_ref(v_vs_2065_);
                        return v___x_2084_;
                    }
                }
            }
            2 => {
                return v___x_2073_;
            }
            3 => {
                return v___x_2077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2___boxed(
    mut v___x_2086_: *mut LeanObject,
    mut v___x_2087_: *mut LeanObject,
    mut v___x_2088_: *mut LeanObject,
    mut v_x_2089_: *mut LeanObject,
    mut v_x_2090_: *mut LeanObject,
    mut v_x_2091_: *mut LeanObject,
    mut v_x_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5156__boxed_2098_: u8 = 0;
    let mut v___x_5157__boxed_2099_: u8 = 0;
    let mut v___x_5158__boxed_2100_: u8 = 0;
    let mut v_x_5160__boxed_2101_: usize = 0;
    let mut v_x_5161__boxed_2102_: usize = 0;
    let mut v_res_2103_: *mut LeanObject = core::ptr::null_mut();
    v___x_5156__boxed_2098_ = (lean_unbox(v___x_2086_) as u8);
    v___x_5157__boxed_2099_ = (lean_unbox(v___x_2087_) as u8);
    v___x_5158__boxed_2100_ = (lean_unbox(v___x_2088_) as u8);
    v_x_5160__boxed_2101_ = lean_unbox_usize(v_x_2090_);
    lean_dec(v_x_2090_);
    v_x_5161__boxed_2102_ = lean_unbox_usize(v_x_2091_);
    lean_dec(v_x_2091_);
    v_res_2103_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_5156__boxed_2098_, v___x_5157__boxed_2099_, v___x_5158__boxed_2100_, v_x_2089_, v_x_5160__boxed_2101_, v_x_5161__boxed_2102_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    lean_dec(v___y_2094_);
    lean_dec_ref(v___y_2093_);
    return v_res_2103_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(
    mut v___x_2104_: u8,
    mut v___x_2105_: u8,
    mut v___x_2106_: u8,
    mut v_t_2107_: *mut LeanObject,
    mut v_init_2108_: *mut LeanObject,
    mut v_start_2109_: *mut LeanObject,
    mut v___y_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
    mut v___y_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    v___x_2115_ = lean_unsigned_to_nat(0);
    v___x_2116_ = lean_nat_dec_eq(v_start_2109_, v___x_2115_);
    if v___x_2116_ == 0 {
        let mut v_root_2117_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_2119_: usize = 0;
        let mut v_tailOff_2120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: u8 = 0;
        v_root_2117_ = lean_ctor_get(v_t_2107_, 0);
        lean_inc_ref(v_root_2117_);
        v_tail_2118_ = lean_ctor_get(v_t_2107_, 1);
        lean_inc_ref(v_tail_2118_);
        v_shift_2119_ = lean_ctor_get_usize(v_t_2107_, 4);
        v_tailOff_2120_ = lean_ctor_get(v_t_2107_, 3);
        lean_inc(v_tailOff_2120_);
        lean_dec_ref(v_t_2107_);
        v___x_2121_ = lean_nat_dec_le(v_tailOff_2120_, v_start_2109_);
        if v___x_2121_ == 0 {
            let mut v___x_2122_: usize = 0;
            let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_2120_);
            v___x_2122_ = lean_usize_of_nat(v_start_2109_);
            v___x_2123_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__2(v___x_2104_, v___x_2105_, v___x_2106_, v_root_2117_, v___x_2122_, v_shift_2119_, v_init_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
            if lean_obj_tag(v___x_2123_) == 0 {
                let mut v_a_2124_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2126_: u8 = 0;
                v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
                lean_inc(v_a_2124_);
                v___x_2125_ = lean_array_get_size(v_tail_2118_);
                v___x_2126_ = lean_nat_dec_lt(v___x_2115_, v___x_2125_);
                if v___x_2126_ == 0 {
                    lean_dec(v_a_2124_);
                    lean_dec_ref(v_tail_2118_);
                    return v___x_2123_;
                } else {
                    let mut v___x_2127_: u8 = 0;
                    v___x_2127_ = lean_nat_dec_le(v___x_2125_, v___x_2125_);
                    if v___x_2127_ == 0 {
                        if v___x_2126_ == 0 {
                            lean_dec(v_a_2124_);
                            lean_dec_ref(v_tail_2118_);
                            return v___x_2123_;
                        } else {
                            let mut v___x_2128_: usize = 0;
                            let mut v___x_2129_: usize = 0;
                            let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_2123_, 1);
                            v___x_2128_ = 0usize;
                            v___x_2129_ = lean_usize_of_nat(v___x_2125_);
                            v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2118_, v___x_2128_, v___x_2129_, v_a_2124_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                            lean_dec_ref(v_tail_2118_);
                            return v___x_2130_;
                        }
                    } else {
                        let mut v___x_2131_: usize = 0;
                        let mut v___x_2132_: usize = 0;
                        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2123_, 1);
                        v___x_2131_ = 0usize;
                        v___x_2132_ = lean_usize_of_nat(v___x_2125_);
                        v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2118_, v___x_2131_, v___x_2132_, v_a_2124_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                        lean_dec_ref(v_tail_2118_);
                        return v___x_2133_;
                    }
                }
            } else {
                lean_dec_ref(v_tail_2118_);
                return v___x_2123_;
            }
        } else {
            let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2136_: u8 = 0;
            lean_dec_ref(v_root_2117_);
            v___x_2134_ = lean_nat_sub(v_start_2109_, v_tailOff_2120_);
            lean_dec(v_tailOff_2120_);
            v___x_2135_ = lean_array_get_size(v_tail_2118_);
            v___x_2136_ = lean_nat_dec_lt(v___x_2134_, v___x_2135_);
            if v___x_2136_ == 0 {
                let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2134_);
                lean_dec_ref(v_tail_2118_);
                v___x_2137_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2137_, 0, v_init_2108_);
                return v___x_2137_;
            } else {
                let mut v___x_2138_: u8 = 0;
                v___x_2138_ = lean_nat_dec_le(v___x_2135_, v___x_2135_);
                if v___x_2138_ == 0 {
                    if v___x_2136_ == 0 {
                        let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_2134_);
                        lean_dec_ref(v_tail_2118_);
                        v___x_2139_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2139_, 0, v_init_2108_);
                        return v___x_2139_;
                    } else {
                        let mut v___x_2140_: usize = 0;
                        let mut v___x_2141_: usize = 0;
                        let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2140_ = lean_usize_of_nat(v___x_2134_);
                        lean_dec(v___x_2134_);
                        v___x_2141_ = lean_usize_of_nat(v___x_2135_);
                        v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2118_, v___x_2140_, v___x_2141_, v_init_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                        lean_dec_ref(v_tail_2118_);
                        return v___x_2142_;
                    }
                } else {
                    let mut v___x_2143_: usize = 0;
                    let mut v___x_2144_: usize = 0;
                    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2143_ = lean_usize_of_nat(v___x_2134_);
                    lean_dec(v___x_2134_);
                    v___x_2144_ = lean_usize_of_nat(v___x_2135_);
                    v___x_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2118_, v___x_2143_, v___x_2144_, v_init_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                    lean_dec_ref(v_tail_2118_);
                    return v___x_2145_;
                }
            }
        }
    } else {
        let mut v_root_2146_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_2147_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
        v_root_2146_ = lean_ctor_get(v_t_2107_, 0);
        lean_inc_ref(v_root_2146_);
        v_tail_2147_ = lean_ctor_get(v_t_2107_, 1);
        lean_inc_ref(v_tail_2147_);
        lean_dec_ref(v_t_2107_);
        v___x_2148_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__4(v___x_2104_, v___x_2105_, v___x_2106_, v_root_2146_, v_init_2108_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
        if lean_obj_tag(v___x_2148_) == 0 {
            let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2151_: u8 = 0;
            v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
            lean_inc(v_a_2149_);
            v___x_2150_ = lean_array_get_size(v_tail_2147_);
            v___x_2151_ = lean_nat_dec_lt(v___x_2115_, v___x_2150_);
            if v___x_2151_ == 0 {
                lean_dec(v_a_2149_);
                lean_dec_ref(v_tail_2147_);
                return v___x_2148_;
            } else {
                let mut v___x_2152_: u8 = 0;
                v___x_2152_ = lean_nat_dec_le(v___x_2150_, v___x_2150_);
                if v___x_2152_ == 0 {
                    if v___x_2151_ == 0 {
                        lean_dec(v_a_2149_);
                        lean_dec_ref(v_tail_2147_);
                        return v___x_2148_;
                    } else {
                        let mut v___x_2153_: usize = 0;
                        let mut v___x_2154_: usize = 0;
                        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_2148_, 1);
                        v___x_2153_ = 0usize;
                        v___x_2154_ = lean_usize_of_nat(v___x_2150_);
                        v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2147_, v___x_2153_, v___x_2154_, v_a_2149_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                        lean_dec_ref(v_tail_2147_);
                        return v___x_2155_;
                    }
                } else {
                    let mut v___x_2156_: usize = 0;
                    let mut v___x_2157_: usize = 0;
                    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_2148_, 1);
                    v___x_2156_ = 0usize;
                    v___x_2157_ = lean_usize_of_nat(v___x_2150_);
                    v___x_2158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3(v___x_2104_, v___x_2105_, v___x_2106_, v_tail_2147_, v___x_2156_, v___x_2157_, v_a_2149_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
                    lean_dec_ref(v_tail_2147_);
                    return v___x_2158_;
                }
            }
        } else {
            lean_dec_ref(v_tail_2147_);
            return v___x_2148_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0___boxed(
    mut v___x_2159_: *mut LeanObject,
    mut v___x_2160_: *mut LeanObject,
    mut v___x_2161_: *mut LeanObject,
    mut v_t_2162_: *mut LeanObject,
    mut v_init_2163_: *mut LeanObject,
    mut v_start_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
    mut v___y_2167_: *mut LeanObject,
    mut v___y_2168_: *mut LeanObject,
    mut v___y_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5282__boxed_2170_: u8 = 0;
    let mut v___x_5283__boxed_2171_: u8 = 0;
    let mut v___x_5284__boxed_2172_: u8 = 0;
    let mut v_res_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_5282__boxed_2170_ = (lean_unbox(v___x_2159_) as u8);
    v___x_5283__boxed_2171_ = (lean_unbox(v___x_2160_) as u8);
    v___x_5284__boxed_2172_ = (lean_unbox(v___x_2161_) as u8);
    v_res_2173_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_5282__boxed_2170_, v___x_5283__boxed_2171_, v___x_5284__boxed_2172_, v_t_2162_, v_init_2163_, v_start_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
    lean_dec(v___y_2168_);
    lean_dec_ref(v___y_2167_);
    lean_dec(v___y_2166_);
    lean_dec_ref(v___y_2165_);
    lean_dec(v_start_2164_);
    return v_res_2173_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(
    mut v___x_2174_: u8,
    mut v___x_2175_: u8,
    mut v___x_2176_: u8,
    mut v_lctx_2177_: *mut LeanObject,
    mut v_init_2178_: *mut LeanObject,
    mut v_start_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    v_decls_2185_ = lean_ctor_get(v_lctx_2177_, 1);
    lean_inc_ref(v_decls_2185_);
    lean_dec_ref(v_lctx_2177_);
    v___x_2186_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0(v___x_2174_, v___x_2175_, v___x_2176_, v_decls_2185_, v_init_2178_, v_start_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    return v___x_2186_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0___boxed(
    mut v___x_2187_: *mut LeanObject,
    mut v___x_2188_: *mut LeanObject,
    mut v___x_2189_: *mut LeanObject,
    mut v_lctx_2190_: *mut LeanObject,
    mut v_init_2191_: *mut LeanObject,
    mut v_start_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5384__boxed_2198_: u8 = 0;
    let mut v___x_5385__boxed_2199_: u8 = 0;
    let mut v___x_5386__boxed_2200_: u8 = 0;
    let mut v_res_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_5384__boxed_2198_ = (lean_unbox(v___x_2187_) as u8);
    v___x_5385__boxed_2199_ = (lean_unbox(v___x_2188_) as u8);
    v___x_5386__boxed_2200_ = (lean_unbox(v___x_2189_) as u8);
    v_res_2201_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(
        v___x_5384__boxed_2198_,
        v___x_5385__boxed_2199_,
        v___x_5386__boxed_2200_,
        v_lctx_2190_,
        v_init_2191_,
        v_start_2192_,
        v___y_2193_,
        v___y_2194_,
        v___y_2195_,
        v___y_2196_,
    );
    lean_dec(v___y_2196_);
    lean_dec_ref(v___y_2195_);
    lean_dec(v___y_2194_);
    lean_dec_ref(v___y_2193_);
    lean_dec(v_start_2192_);
    return v_res_2201_;
}
pub unsafe fn l_Lean_Meta_ppGoal___lam__0(
    mut v___x_2205_: u8,
    mut v___x_2206_: u8,
    mut v___x_2207_: u8,
    mut v_fst_2208_: *mut LeanObject,
    mut v___x_2209_: *mut LeanObject,
    mut v___x_2210_: *mut LeanObject,
    mut v___x_2211_: *mut LeanObject,
    mut v_type_2212_: *mut LeanObject,
    mut v_val_2213_: *mut LeanObject,
    mut v_userName_2214_: *mut LeanObject,
    mut v___y_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v_fst_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_isSharedCheck_2278_: u8 = 0;
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = l_Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0(
                    v___x_2205_,
                    v___x_2206_,
                    v___x_2207_,
                    v_fst_2208_,
                    v___x_2209_,
                    v___x_2210_,
                    v___y_2215_,
                    v___y_2216_,
                    v___y_2217_,
                    v___y_2218_,
                );
                if lean_obj_tag(v___x_2220_) == 0 {
                    v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
                    lean_inc(v_a_2221_);
                    lean_dec_ref_known(v___x_2220_, 1);
                    v_snd_2222_ = lean_ctor_get(v_a_2221_, 1);
                    v_fst_2223_ = lean_ctor_get(v_a_2221_, 0);
                    v_isSharedCheck_2280_ = (!lean_is_exclusive(v_a_2221_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2225_ = v_a_2221_;
                        v_isShared_2226_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2222_);
                        lean_inc(v_fst_2223_);
                        lean_dec(v_a_2221_);
                        v___x_2225_ = lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_userName_2214_);
                    lean_dec_ref(v_type_2212_);
                    lean_dec(v___x_2211_);
                    v_a_2281_ = lean_ctor_get(v___x_2220_, 0);
                    v_isSharedCheck_2288_ = (!lean_is_exclusive(v___x_2220_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v___x_2283_ = v___x_2220_;
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_2281_);
                        lean_dec(v___x_2220_);
                        v___x_2283_ = lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2288_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2227_ = lean_ctor_get(v_snd_2222_, 0);
                v_snd_2228_ = lean_ctor_get(v_snd_2222_, 1);
                v_isSharedCheck_2279_ = (!lean_is_exclusive(v_snd_2222_)) as u8;
                if v_isSharedCheck_2279_ == 0 {
                    v___x_2230_ = v_snd_2222_;
                    v_isShared_2231_ = v_isSharedCheck_2279_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2228_);
                    lean_inc(v_fst_2227_);
                    lean_dec(v_snd_2222_);
                    v___x_2230_ = lean_box(0);
                    v_isShared_2231_ = v_isSharedCheck_2279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v___x_2211_);
                v___x_2232_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_pushPending(
                    v___x_2211_,
                    v_fst_2223_,
                    v_fst_2227_,
                    v_snd_2228_,
                    v___y_2215_,
                    v___y_2216_,
                    v___y_2217_,
                    v___y_2218_,
                );
                if lean_obj_tag(v___x_2232_) == 0 {
                    v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
                    v_isSharedCheck_2278_ = (!lean_is_exclusive(v___x_2232_)) as u8;
                    if v_isSharedCheck_2278_ == 0 {
                        v___x_2235_ = v___x_2232_;
                        v_isShared_2236_ = v_isSharedCheck_2278_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2233_);
                        lean_dec(v___x_2232_);
                        v___x_2235_ = lean_box(0);
                        v_isShared_2236_ = v_isSharedCheck_2278_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2230_);
                    lean_del_object(v___x_2225_);
                    lean_dec(v_userName_2214_);
                    lean_dec_ref(v_type_2212_);
                    lean_dec(v___x_2211_);
                    return v___x_2232_;
                }
            }
            3 => {
                v___x_2237_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_PPGoal_0__Lean_Meta_ppGoal_ppVars_spec__0___redArg(v_type_2212_, v___y_2216_);
                v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
                v_isSharedCheck_2277_ = (!lean_is_exclusive(v___x_2237_)) as u8;
                if v_isSharedCheck_2277_ == 0 {
                    v___x_2240_ = v___x_2237_;
                    v_isShared_2241_ = v_isSharedCheck_2277_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_2238_);
                    lean_dec(v___x_2237_);
                    v___x_2240_ = lean_box(0);
                    v_isShared_2241_ = v_isSharedCheck_2277_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2242_ = l_Lean_Meta_ppExpr(
                    v_a_2238_,
                    v___y_2215_,
                    v___y_2216_,
                    v___y_2217_,
                    v___y_2218_,
                );
                if lean_obj_tag(v___x_2242_) == 0 {
                    v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
                    v_isSharedCheck_2276_ = (!lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v___x_2245_ = v___x_2242_;
                        v_isShared_2246_ = v_isSharedCheck_2276_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2243_);
                        lean_dec(v___x_2242_);
                        v___x_2245_ = lean_box(0);
                        v_isShared_2246_ = v_isSharedCheck_2276_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2240_);
                    lean_del_object(v___x_2235_);
                    lean_dec(v_a_2233_);
                    lean_del_object(v___x_2230_);
                    lean_del_object(v___x_2225_);
                    lean_dec(v_userName_2214_);
                    lean_dec(v___x_2211_);
                    return v___x_2242_;
                }
            }
            5 => {
                v___x_2247_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine(v_a_2233_);
                v___x_2248_ = l_Lean_Meta_getGoalPrefix(v_val_2213_);
                if v_isShared_2241_ == 0 {
                    lean_ctor_set_tag(v___x_2240_, 3);
                    lean_ctor_set(v___x_2240_, 0, v___x_2248_);
                    v___x_2250_ = v___x_2240_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2248_);
                    v___x_2250_ = v_reuseFailAlloc_2275_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2231_ == 0 {
                    lean_ctor_set_tag(v___x_2230_, 5);
                    lean_ctor_set(v___x_2230_, 1, v___x_2250_);
                    lean_ctor_set(v___x_2230_, 0, v___x_2247_);
                    v___x_2252_ = v___x_2230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2247_);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2250_);
                    v___x_2252_ = v_reuseFailAlloc_2274_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2226_ == 0 {
                    lean_ctor_set_tag(v___x_2225_, 4);
                    lean_ctor_set(v___x_2225_, 1, v_a_2243_);
                    lean_ctor_set(v___x_2225_, 0, v___x_2211_);
                    v___x_2254_ = v___x_2225_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2211_);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_a_2243_);
                    v___x_2254_ = v_reuseFailAlloc_2273_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2255_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2255_, 0, v___x_2252_);
                lean_ctor_set(v___x_2255_, 1, v___x_2254_);
                if lean_obj_tag(v_userName_2214_) == 0 {
                    lean_del_object(v___x_2235_);
                    if v_isShared_2246_ == 0 {
                        lean_ctor_set(v___x_2245_, 0, v___x_2255_);
                        v___x_2257_ = v___x_2245_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
                        v___x_2257_ = v_reuseFailAlloc_2258_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_2259_ = l_Lean_Meta_ppGoal___lam__0___closed__1;
                    v___x_2260_ = lean_erase_macro_scopes(v_userName_2214_);
                    v___x_2261_ = 1;
                    v___x_2262_ = l_Lean_Name_toString(v___x_2260_, v___x_2261_);
                    if v_isShared_2236_ == 0 {
                        lean_ctor_set_tag(v___x_2235_, 3);
                        lean_ctor_set(v___x_2235_, 0, v___x_2262_);
                        v___x_2264_ = v___x_2235_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2272_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2262_);
                        v___x_2264_ = v_reuseFailAlloc_2272_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2257_;
            }
            10 => {
                v___x_2265_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2265_, 0, v___x_2259_);
                lean_ctor_set(v___x_2265_, 1, v___x_2264_);
                v___x_2266_ = l___private_Lean_Meta_PPGoal_0__Lean_Meta_addLine___closed__1;
                v___x_2267_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2267_, 0, v___x_2265_);
                lean_ctor_set(v___x_2267_, 1, v___x_2266_);
                v___x_2268_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2268_, 0, v___x_2267_);
                lean_ctor_set(v___x_2268_, 1, v___x_2255_);
                if v_isShared_2246_ == 0 {
                    lean_ctor_set(v___x_2245_, 0, v___x_2268_);
                    v___x_2270_ = v___x_2245_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
                    v___x_2270_ = v_reuseFailAlloc_2271_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2270_;
            }
            12 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_ppGoal___lam__0___boxed(
    mut v___x_2289_: *mut LeanObject,
    mut v___x_2290_: *mut LeanObject,
    mut v___x_2291_: *mut LeanObject,
    mut v_fst_2292_: *mut LeanObject,
    mut v___x_2293_: *mut LeanObject,
    mut v___x_2294_: *mut LeanObject,
    mut v___x_2295_: *mut LeanObject,
    mut v_type_2296_: *mut LeanObject,
    mut v_val_2297_: *mut LeanObject,
    mut v_userName_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5419__boxed_2304_: u8 = 0;
    let mut v___x_5420__boxed_2305_: u8 = 0;
    let mut v___x_5421__boxed_2306_: u8 = 0;
    let mut v_res_2307_: *mut LeanObject = core::ptr::null_mut();
    v___x_5419__boxed_2304_ = (lean_unbox(v___x_2289_) as u8);
    v___x_5420__boxed_2305_ = (lean_unbox(v___x_2290_) as u8);
    v___x_5421__boxed_2306_ = (lean_unbox(v___x_2291_) as u8);
    v_res_2307_ = l_Lean_Meta_ppGoal___lam__0(
        v___x_5419__boxed_2304_,
        v___x_5420__boxed_2305_,
        v___x_5421__boxed_2306_,
        v_fst_2292_,
        v___x_2293_,
        v___x_2294_,
        v___x_2295_,
        v_type_2296_,
        v_val_2297_,
        v_userName_2298_,
        v___y_2299_,
        v___y_2300_,
        v___y_2301_,
        v___y_2302_,
    );
    lean_dec(v___y_2302_);
    lean_dec_ref(v___y_2301_);
    lean_dec(v___y_2300_);
    lean_dec_ref(v___y_2299_);
    lean_dec_ref(v_val_2297_);
    lean_dec(v___x_2294_);
    return v_res_2307_;
}
pub unsafe fn l_Lean_Meta_ppGoal(
    mut v_mvarId_2317_: *mut LeanObject,
    mut v_a_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
    mut v_a_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    v___x_2323_ = lean_st_ref_get(v_a_2319_);
    v_mctx_2324_ = lean_ctor_get(v___x_2323_, 0);
    lean_inc_ref(v_mctx_2324_);
    lean_dec(v___x_2323_);
    v___x_2325_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_2324_, v_mvarId_2317_);
    lean_dec_ref(v_mctx_2324_);
    if lean_obj_tag(v___x_2325_) == 0 {
        let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
        v___x_2326_ = l_Lean_Meta_ppGoal___closed__1;
        v___x_2327_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2327_, 0, v___x_2326_);
        return v___x_2327_;
    } else {
        let mut v_val_2328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_options_2329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_userName_2330_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lctx_2331_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2332_: *mut LeanObject = core::ptr::null_mut();
        let mut v_localInstances_2333_: *mut LeanObject = core::ptr::null_mut();
        let mut v_kind_2334_: u8 = 0;
        let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2336_: u8 = 0;
        let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2338_: u8 = 0;
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_2342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: u8 = 0;
        let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
        v_val_2328_ = lean_ctor_get(v___x_2325_, 0);
        lean_inc(v_val_2328_);
        lean_dec_ref_known(v___x_2325_, 1);
        v_options_2329_ = lean_ctor_get(v_a_2320_, 2);
        v_userName_2330_ = lean_ctor_get(v_val_2328_, 0);
        lean_inc(v_userName_2330_);
        v_lctx_2331_ = lean_ctor_get(v_val_2328_, 1);
        v_type_2332_ = lean_ctor_get(v_val_2328_, 2);
        lean_inc_ref(v_type_2332_);
        v_localInstances_2333_ = lean_ctor_get(v_val_2328_, 4);
        lean_inc_ref(v_localInstances_2333_);
        v_kind_2334_ = lean_ctor_get_uint8(
            v_val_2328_,
            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        );
        v___x_2335_ = l_Lean_Meta_pp_auxDecls;
        v___x_2336_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(
            v_options_2329_,
            v___x_2335_,
        );
        v___x_2337_ = l_Lean_Meta_pp_implementationDetailHyps;
        v___x_2338_ = l_Lean_Option_get___at___00Lean_Meta_ppGoal_shouldShowLetValue_spec__0(
            v_options_2329_,
            v___x_2337_,
        );
        v___x_2339_ = lean_box(1);
        lean_inc_ref(v_options_2329_);
        v___x_2340_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_2340_, 0, v_options_2329_);
        lean_ctor_set(v___x_2340_, 1, v___x_2339_);
        lean_ctor_set(v___x_2340_, 2, v___x_2339_);
        lean_inc_ref(v_lctx_2331_);
        v___x_2341_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2331_, v___x_2340_);
        v_fst_2342_ = lean_ctor_get(v___x_2341_, 0);
        lean_inc_n(v_fst_2342_, 2);
        lean_dec_ref(v___x_2341_);
        v___x_2343_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Meta_ppGoal_spec__0_spec__0_spec__3___closed__0);
        v___x_2344_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_2334_);
        v___x_2345_ = l_Lean_Meta_ppGoal___closed__3;
        v___x_2346_ = lean_unsigned_to_nat(0);
        v___x_2347_ = lean_box((v___x_2338_) as usize);
        v___x_2348_ = lean_box((v___x_2344_) as usize);
        v___x_2349_ = lean_box((v___x_2336_) as usize);
        v___f_2350_ = lean_alloc_closure(
            l_Lean_Meta_ppGoal___lam__0___boxed as *mut core::ffi::c_void,
            15,
            10,
        );
        lean_closure_set(v___f_2350_, 0, v___x_2347_);
        lean_closure_set(v___f_2350_, 1, v___x_2348_);
        lean_closure_set(v___f_2350_, 2, v___x_2349_);
        lean_closure_set(v___f_2350_, 3, v_fst_2342_);
        lean_closure_set(v___f_2350_, 4, v___x_2345_);
        lean_closure_set(v___f_2350_, 5, v___x_2346_);
        lean_closure_set(v___f_2350_, 6, v___x_2343_);
        lean_closure_set(v___f_2350_, 7, v_type_2332_);
        lean_closure_set(v___f_2350_, 8, v_val_2328_);
        lean_closure_set(v___f_2350_, 9, v_userName_2330_);
        v___x_2351_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_ppGoal_spec__1___redArg(
            v_fst_2342_,
            v_localInstances_2333_,
            v___f_2350_,
            v_a_2318_,
            v_a_2319_,
            v_a_2320_,
            v_a_2321_,
        );
        return v___x_2351_;
    }
}
pub unsafe fn l_Lean_Meta_ppGoal___boxed(
    mut v_mvarId_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
    mut v_a_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_res_2358_ = l_Lean_Meta_ppGoal(v_mvarId_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
    lean_dec(v_a_2356_);
    lean_dec_ref(v_a_2355_);
    lean_dec(v_a_2354_);
    lean_dec_ref(v_a_2353_);
    lean_dec(v_mvarId_2352_);
    return v_res_2358_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_PPGoal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_4182071446____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_auxDecls = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_auxDecls);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3119699492____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_implementationDetailHyps = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_implementationDetailHyps);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3613105029____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_inaccessibleNames = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_inaccessibleNames);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3896890698____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_showLetValues = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_showLetValues);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_1112997472____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_showLetValues_threshold = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_showLetValues_threshold);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_PPGoal_0__Lean_Meta_initFn_00___x40_Lean_Meta_PPGoal_3655794009____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_pp_showLetValues_tactic_threshold = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_pp_showLetValues_tactic_threshold);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_PPGoal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_PPGoal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_PPGoal(builtin);
}
