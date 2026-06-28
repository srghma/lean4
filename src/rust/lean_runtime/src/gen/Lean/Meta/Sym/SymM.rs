// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: Lean.Meta.Sym.AlphaShareCommon Lean.Meta.CongrTheorems
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed,
    l_StateRefT_x27_instMonadExceptOf___redArg___lam__2,
    l_StateRefT_x27_instMonadFunctor___aux__1___boxed, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node5, l_Lean_addMacroScope,
    l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed,
    l_ReaderT_instMonadExceptOf___redArg___lam__2, l_ReaderT_instMonadFunctor___lam__0,
    l_ReaderT_instMonadLift___lam__0___boxed, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_instMonadQuotationCoreM, l_Lean_instMonadExceptOfExceptionCoreM,
};
use crate::r#gen::Lean::Data::KVMap::l_Lean_KVMap_instValueBool;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Option_get___redArg, lean_register_option};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg,
    l_Lean_throwError___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_Int_mkType, l_Lean_mkConst, l_Lean_mkNatLit};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instAddMessageContextMetaM, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isDefEqI,
};
use crate::r#gen::Lean::Meta::CongrTheorems::{
    initialize_Lean_Meta_CongrTheorems, runtime_initialize_Lean_Meta_CongrTheorems,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareCommon::{
    initialize_Lean_Meta_Sym_AlphaShareCommon,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go,
    runtime_initialize_Lean_Meta_Sym_AlphaShareCommon,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,16563840882919605222 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,12705026313358803449 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 104, 101, 99, 107, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,17711119471907869950 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,6218173260972607057 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 115, 117, 101, 115, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,16563840882919605222 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,13379912757096045311 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4607919608188261591 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 121, 109, 77, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,16875470911029737534 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,11726973394908900231 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,1267766208074481146 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,5379550515515746046 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,2529073834662971127 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,2398512038427916102 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,6594316647550557687 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,5876541111662122634 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4903966020297646382 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,12573723659802585063 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject,3401488681846805806 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
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
static mut l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_SymExtensionStateSpec: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedSymExtensionState: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value: LeanStringObject<92> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 92,
        m_capacity: 92,
        m_length: 91,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114,
            32, 96, 83, 121, 109, 96, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 44, 32, 101,
            120, 116, 101, 110, 115, 105, 111, 110, 115, 32, 99, 97, 110, 32, 111, 110, 108, 121,
            32, 98, 101, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 100, 117, 114,
            105, 110, 103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110,
            0,
        ],
    };
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut LeanObject],
};
static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
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
static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedConfig_default: u8 = 0;
pub static mut l_Lean_Meta_Sym_instInhabitedConfig: u8 = 0;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value
        ) as *mut LeanObject,
        907667957179513571 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [66, 111, 111, 108, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
        ) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value
        ) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
        ) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value
        ) as *mut LeanObject,
        9255189395584251158 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [79, 114, 100, 101, 114, 105, 110, 103, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value:
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
    m_data: [101, 113, 0],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value
        ) as *mut LeanObject,
        5208578977668345058 as *mut LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value
        ) as *mut LeanObject,
        5594775977794639463 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 115, 115, 117, 101, 0],
};
static mut l_Lean_Meta_Sym_reportIssue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__0_value) as *mut LeanObject,
        17036113238723837529 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_reportIssue___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_reportIssue___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_reportIssue___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_reportIssue___closed__3_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Meta_Sym_reportIssue___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__3_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_reportIssue___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_reportIssue___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_reportIssue___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value) as *mut LeanObject,5573444893818005634 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [83, 121, 109, 46, 114, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 73, 102, 86, 101, 114, 98, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [114, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 73, 102, 86, 101, 114, 98, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,12237061437965074038 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value) as *mut LeanObject,11405738229328456530 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value) as *mut LeanObject,2994568011185431995 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value) as *mut LeanObject,14298422259736409839 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24:
    *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value) as *mut LeanObject,11510953549444071797 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value) as *mut LeanObject,491622604497152460 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 77, 33, 95, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value
) as *mut LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value) as *mut LeanObject,13317951319906582257 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 33, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value
) as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            100, 111, 69, 108, 101, 109, 82, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 33,
            95, 95, 0,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value)
                as *mut LeanObject,
            3146137996699014428 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value)
                as *mut LeanObject,
            12571085391447129896 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [114, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 33, 0],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 114, 101, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value)
                as *mut LeanObject,
            393173242845875278 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value)
                as *mut LeanObject,
            18163029821153688220 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 101, 114, 109, 0],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value)
                as *mut LeanObject,
            8609355255726335675 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 7,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_doElemReportIssue_x21____: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            83, 121, 109, 46, 114, 101, 112, 111, 114, 116, 68, 98, 103, 73, 115, 115, 117, 101, 0,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            114, 101, 112, 111, 114, 116, 68, 98, 103, 73, 115, 115, 117, 101, 0,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,12237061437965074038 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
                as *mut LeanObject,
            4429398455170599012 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
                as *mut LeanObject,
            18355236360871851557 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            100, 111, 69, 108, 101, 109, 82, 101, 112, 111, 114, 116, 68, 98, 103, 73, 115, 115,
            117, 101, 33, 95, 95, 0,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut LeanObject,4034176598647545331 as *mut LeanObject] };
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value)
                as *mut LeanObject,
            5603533687169962240 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            114, 101, 112, 111, 114, 116, 68, 98, 103, 73, 115, 115, 117, 101, 33, 0,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value)
                as *mut LeanObject,
            (((1022 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21____: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value: LeanClosureObject<0> =
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
        m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value: LeanClosureObject<0> =
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
        m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__26: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            60, 83, 121, 109, 77, 32, 100, 101, 102, 97, 117, 108, 116, 32, 118, 97, 108, 117, 101,
            62, 0,
        ],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__29: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(
    mut v_name_2641_: *mut LeanObject,
    mut v_decl_2642_: *mut LeanObject,
    mut v_ref_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_unused_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2645_ = lean_ctor_get(v_decl_2642_, 0);
                v_descr_2646_ = lean_ctor_get(v_decl_2642_, 1);
                v_deprecation_x3f_2647_ = lean_ctor_get(v_decl_2642_, 2);
                v___x_2648_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2649_ = (lean_unbox(v_defValue_2645_) as u8);
                lean_ctor_set_uint8(v___x_2648_, 0 as u32, v___x_2649_);
                lean_inc(v_deprecation_x3f_2647_);
                lean_inc_ref(v_descr_2646_);
                lean_inc_n(v_name_2641_, 2);
                v___x_2650_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2650_, 0, v_name_2641_);
                lean_ctor_set(v___x_2650_, 1, v_ref_2643_);
                lean_ctor_set(v___x_2650_, 2, v___x_2648_);
                lean_ctor_set(v___x_2650_, 3, v_descr_2646_);
                lean_ctor_set(v___x_2650_, 4, v_deprecation_x3f_2647_);
                v___x_2651_ = lean_register_option(v_name_2641_, v___x_2650_);
                if lean_obj_tag(v___x_2651_) == 0 {
                    v_isSharedCheck_2659_ = (!lean_is_exclusive(v___x_2651_)) as u8;
                    if v_isSharedCheck_2659_ == 0 {
                        v_unused_2660_ = lean_ctor_get(v___x_2651_, 0);
                        lean_dec(v_unused_2660_);
                        v___x_2653_ = v___x_2651_;
                        v_isShared_2654_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2651_);
                        v___x_2653_ = lean_box(0);
                        v_isShared_2654_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_2641_);
                    v_a_2661_ = lean_ctor_get(v___x_2651_, 0);
                    v_isSharedCheck_2668_ = (!lean_is_exclusive(v___x_2651_)) as u8;
                    if v_isSharedCheck_2668_ == 0 {
                        v___x_2663_ = v___x_2651_;
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2661_);
                        lean_dec(v___x_2651_);
                        v___x_2663_ = lean_box(0);
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_2645_);
                v___x_2655_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2655_, 0, v_name_2641_);
                lean_ctor_set(v___x_2655_, 1, v_defValue_2645_);
                if v_isShared_2654_ == 0 {
                    lean_ctor_set(v___x_2653_, 0, v___x_2655_);
                    v___x_2657_ = v___x_2653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
                    v___x_2657_ = v_reuseFailAlloc_2658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2657_;
            }
            3 => {
                if v_isShared_2664_ == 0 {
                    v___x_2666_ = v___x_2663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2669_: *mut LeanObject,
    mut v_decl_2670_: *mut LeanObject,
    mut v_ref_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_2669_, v_decl_2670_, v_ref_2671_);
    lean_dec_ref(v_decl_2670_);
    return v_res_2673_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    v___x_2695_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2696_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2697_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2698_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_2695_, v___x_2696_, v___x_2697_);
    return v___x_2698_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(
    mut v_a_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2700_: *mut LeanObject = core::ptr::null_mut();
    v_res_2700_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
    return v_res_2700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = lean_unsigned_to_nat(2410647589);
    v___x_2755_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2756_ = l_Lean_Name_num___override(v___x_2755_, v___x_2754_);
    return v___x_2756_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2759_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2760_ = l_Lean_Name_str___override(v___x_2759_, v___x_2758_);
    return v___x_2760_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    v___x_2762_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2763_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2764_ = l_Lean_Name_str___override(v___x_2763_, v___x_2762_);
    return v___x_2764_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    v___x_2765_ = lean_unsigned_to_nat(2);
    v___x_2766_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2767_ = l_Lean_Name_num___override(v___x_2766_, v___x_2765_);
    return v___x_2767_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    v___x_2769_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2770_ = 0;
    v___x_2771_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2772_ = l_Lean_registerTraceClass(v___x_2769_, v___x_2770_, v___x_2771_);
    return v___x_2772_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(
    mut v_a_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
    return v_res_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState() -> *mut LeanObject {
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_Meta_Sym_SymExtensionStateSpec;
    v_snd_2779_ = lean_ctor_get(v___x_2778_, 1);
    lean_inc(v_snd_2779_);
    return v_snd_2779_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0() -> *mut LeanObject {
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v___x_2784_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1;
    v___x_2785_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2785_, 0, v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2787_: *mut LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
    return v_res_2787_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default(
    mut v_00_u03c3_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    v___x_2793_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1;
    return v___x_2793_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0() -> *mut LeanObject {
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default(lean_box(0));
    return v___x_2794_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension(
    mut v_a_2795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    v___x_2796_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0,
    );
    return v___x_2796_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    v___x_2800_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_;
    v___x_2801_ = lean_st_mk_ref(v___x_2800_);
    v___x_2802_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2802_, 0, v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(
    mut v_a_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2804_: *mut LeanObject = core::ptr::null_mut();
    v_res_2804_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
    return v_res_2804_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(
    mut v_ext_2805_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_ext_2805_);
    return v_ext_2805_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(
    mut v_ext_2806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2807_: *mut LeanObject = core::ptr::null_mut();
    v_res_2807_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(
            v_ext_2806_,
        );
    lean_dec_ref(v_ext_2806_);
    return v_res_2807_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(
    mut v_00_u03c3_2808_: *mut LeanObject,
    mut v_ext_2809_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_ext_2809_);
    return v_ext_2809_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(
    mut v_00_u03c3_2810_: *mut LeanObject,
    mut v_ext_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(
        v_00_u03c3_2810_,
        v_ext_2811_,
    );
    lean_dec_ref(v_ext_2811_);
    return v_res_2812_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    v___x_2814_ = l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0;
    v___x_2815_ = lean_mk_io_user_error(v___x_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension___redArg(
    mut v_mkInitial_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2838_: u8 = 0;
    let mut v_a_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2818_ = l_Lean_initializing();
                if lean_obj_tag(v___x_2818_) == 0 {
                    v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
                    v_isSharedCheck_2838_ = (!lean_is_exclusive(v___x_2818_)) as u8;
                    if v_isSharedCheck_2838_ == 0 {
                        v___x_2821_ = v___x_2818_;
                        v_isShared_2822_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2819_);
                        lean_dec(v___x_2818_);
                        v___x_2821_ = lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_mkInitial_2816_);
                    v_a_2839_ = lean_ctor_get(v___x_2818_, 0);
                    v_isSharedCheck_2846_ = (!lean_is_exclusive(v___x_2818_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v___x_2841_ = v___x_2818_;
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2839_);
                        lean_dec(v___x_2818_);
                        v___x_2841_ = lean_box(0);
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2823_ = (lean_unbox(v_a_2819_) as u8);
                lean_dec(v_a_2819_);
                if v___x_2823_ == 0 {
                    lean_dec_ref(v_mkInitial_2816_);
                    v___x_2824_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1,
                    );
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set_tag(v___x_2821_, 1);
                        lean_ctor_set(v___x_2821_, 0, v___x_2824_);
                        v___x_2826_ = v___x_2821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2828_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
                    v___x_2829_ = lean_st_ref_get(v___x_2828_);
                    v___x_2830_ = lean_st_ref_take(v___x_2828_);
                    v___x_2831_ = lean_array_get_size(v___x_2829_);
                    lean_dec(v___x_2829_);
                    v___x_2832_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2832_, 0, v___x_2831_);
                    lean_ctor_set(v___x_2832_, 1, v_mkInitial_2816_);
                    lean_inc_ref(v___x_2832_);
                    v___x_2833_ = lean_array_push(v___x_2830_, v___x_2832_);
                    v___x_2834_ = lean_st_ref_set(v___x_2828_, v___x_2833_);
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set(v___x_2821_, 0, v___x_2832_);
                        v___x_2836_ = v___x_2821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2832_);
                        v___x_2836_ = v_reuseFailAlloc_2837_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2826_;
            }
            3 => {
                return v___x_2836_;
            }
            4 => {
                if v_isShared_2842_ == 0 {
                    v___x_2844_ = v___x_2841_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension___redArg___boxed(
    mut v_mkInitial_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2849_: *mut LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension(
    mut v_00_u03c3_2850_: *mut LeanObject,
    mut v_mkInitial_2851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_2851_);
    return v___x_2853_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension___boxed(
    mut v_00_u03c3_2854_: *mut LeanObject,
    mut v_mkInitial_2855_: *mut LeanObject,
    mut v_a_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2857_: *mut LeanObject = core::ptr::null_mut();
    v_res_2857_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_2854_, v_mkInitial_2855_);
    return v_res_2857_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(
    mut v_sz_2858_: usize,
    mut v_i_2859_: usize,
    mut v_bs_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mkInitial_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: usize = 0;
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2877_: u8 = 0;
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2862_ = lean_usize_dec_lt(v_i_2859_, v_sz_2858_);
                if v___x_2862_ == 0 {
                    v___x_2863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2863_, 0, v_bs_2860_);
                    return v___x_2863_;
                } else {
                    v_v_2864_ = lean_array_uget_borrowed(v_bs_2860_, v_i_2859_);
                    v_mkInitial_2865_ = lean_ctor_get(v_v_2864_, 1);
                    lean_inc_ref(v_mkInitial_2865_);
                    v___x_2866_ = lean_apply_1(v_mkInitial_2865_, lean_box(0));
                    if lean_obj_tag(v___x_2866_) == 0 {
                        v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
                        lean_inc(v_a_2867_);
                        lean_dec_ref_known(v___x_2866_, 1);
                        v___x_2868_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2869_ = lean_array_uset(v_bs_2860_, v_i_2859_, v___x_2868_);
                        v___x_2870_ = 1usize;
                        v___x_2871_ = lean_usize_add(v_i_2859_, v___x_2870_);
                        v___x_2872_ = lean_array_uset(v_bs_x27_2869_, v_i_2859_, v_a_2867_);
                        v_i_2859_ = v___x_2871_;
                        v_bs_2860_ = v___x_2872_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2860_);
                        v_a_2874_ = lean_ctor_get(v___x_2866_, 0);
                        v_isSharedCheck_2881_ = (!lean_is_exclusive(v___x_2866_)) as u8;
                        if v_isSharedCheck_2881_ == 0 {
                            v___x_2876_ = v___x_2866_;
                            v_isShared_2877_ = v_isSharedCheck_2881_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2874_);
                            lean_dec(v___x_2866_);
                            v___x_2876_ = lean_box(0);
                            v_isShared_2877_ = v_isSharedCheck_2881_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2877_ == 0 {
                    v___x_2879_ = v___x_2876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
                    v___x_2879_ = v_reuseFailAlloc_2880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0___boxed(
    mut v_sz_2882_: *mut LeanObject,
    mut v_i_2883_: *mut LeanObject,
    mut v_bs_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2886_: usize = 0;
    let mut v_i_boxed_2887_: usize = 0;
    let mut v_res_2888_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2886_ = lean_unbox_usize(v_sz_2882_);
    lean_dec(v_sz_2882_);
    v_i_boxed_2887_ = lean_unbox_usize(v_i_2883_);
    lean_dec(v_i_2883_);
    v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_2886_, v_i_boxed_2887_, v_bs_2884_);
    return v_res_2888_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtensions_mkInitialStates() -> *mut LeanObject {
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2892_: usize = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2890_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
    v___x_2891_ = lean_st_ref_get(v___x_2890_);
    v_sz_2892_ = lean_array_size(v___x_2891_);
    v___x_2893_ = 0usize;
    v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_2892_, v___x_2893_, v___x_2891_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(
    mut v_a_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2896_: *mut LeanObject = core::ptr::null_mut();
    v_res_2896_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
    return v_res_2896_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorIdx(mut v_x_2905_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_2905_) {
        0 => {
            let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
            v___x_2906_ = lean_unsigned_to_nat(0);
            return v___x_2906_;
        }
        1 => {
            let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
            v___x_2907_ = lean_unsigned_to_nat(1);
            return v___x_2907_;
        }
        2 => {
            let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
            v___x_2908_ = lean_unsigned_to_nat(2);
            return v___x_2908_;
        }
        _ => {
            let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
            v___x_2909_ = lean_unsigned_to_nat(3);
            return v___x_2909_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(
    mut v_x_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2911_: *mut LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_2910_);
    lean_dec(v_x_2910_);
    return v_res_2911_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(
    mut v_t_2912_: *mut LeanObject,
    mut v_k_2913_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_2912_) {
        0 => {
            return v_k_2913_;
        }
        1 => {
            let mut v_prefixSize_2914_: *mut LeanObject = core::ptr::null_mut();
            let mut v_suffixSize_2915_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
            v_prefixSize_2914_ = lean_ctor_get(v_t_2912_, 0);
            lean_inc(v_prefixSize_2914_);
            v_suffixSize_2915_ = lean_ctor_get(v_t_2912_, 1);
            lean_inc(v_suffixSize_2915_);
            lean_dec_ref_known(v_t_2912_, 2);
            v___x_2916_ = lean_apply_2(v_k_2913_, v_prefixSize_2914_, v_suffixSize_2915_);
            return v___x_2916_;
        }
        _ => {
            let mut v_rewritable_2917_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
            v_rewritable_2917_ = lean_ctor_get(v_t_2912_, 0);
            lean_inc_ref(v_rewritable_2917_);
            lean_dec(v_t_2912_);
            v___x_2918_ = lean_apply_1(v_k_2913_, v_rewritable_2917_);
            return v___x_2918_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim(
    mut v_motive_2919_: *mut LeanObject,
    mut v_ctorIdx_2920_: *mut LeanObject,
    mut v_t_2921_: *mut LeanObject,
    mut v_h_2922_: *mut LeanObject,
    mut v_k_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2921_, v_k_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(
    mut v_motive_2925_: *mut LeanObject,
    mut v_ctorIdx_2926_: *mut LeanObject,
    mut v_t_2927_: *mut LeanObject,
    mut v_h_2928_: *mut LeanObject,
    mut v_k_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2930_: *mut LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(
        v_motive_2925_,
        v_ctorIdx_2926_,
        v_t_2927_,
        v_h_2928_,
        v_k_2929_,
    );
    lean_dec(v_ctorIdx_2926_);
    return v_res_2930_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(
    mut v_t_2931_: *mut LeanObject,
    mut v_none_2932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v___x_2933_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2931_, v_none_2932_);
    return v___x_2933_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_none_elim(
    mut v_motive_2934_: *mut LeanObject,
    mut v_t_2935_: *mut LeanObject,
    mut v_h_2936_: *mut LeanObject,
    mut v_none_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    v___x_2938_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2935_, v_none_2937_);
    return v___x_2938_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(
    mut v_t_2939_: *mut LeanObject,
    mut v_fixedPrefix_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v___x_2941_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2939_, v_fixedPrefix_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(
    mut v_motive_2942_: *mut LeanObject,
    mut v_t_2943_: *mut LeanObject,
    mut v_h_2944_: *mut LeanObject,
    mut v_fixedPrefix_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    v___x_2946_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2943_, v_fixedPrefix_2945_);
    return v___x_2946_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(
    mut v_t_2947_: *mut LeanObject,
    mut v_interlaced_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2947_, v_interlaced_2948_);
    return v___x_2949_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_interlaced_elim(
    mut v_motive_2950_: *mut LeanObject,
    mut v_t_2951_: *mut LeanObject,
    mut v_h_2952_: *mut LeanObject,
    mut v_interlaced_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2951_, v_interlaced_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(
    mut v_t_2955_: *mut LeanObject,
    mut v_congrTheorem_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    v___x_2957_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2955_, v_congrTheorem_2956_);
    return v___x_2957_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(
    mut v_motive_2958_: *mut LeanObject,
    mut v_t_2959_: *mut LeanObject,
    mut v_h_2960_: *mut LeanObject,
    mut v_congrTheorem_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2959_, v_congrTheorem_2961_);
    return v___x_2962_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedConfig_default() -> u8 {
    let mut v___x_2963_: u8 = 0;
    v___x_2963_ = 1;
    return v___x_2963_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedConfig() -> u8 {
    let mut v___x_2964_: u8 = 0;
    v___x_2964_ = 1;
    return v___x_2964_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2()
-> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = lean_box(0);
    v___x_2969_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1;
    v___x_2970_ = l_Lean_mkConst(v___x_2969_, v___x_2968_);
    return v___x_2970_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5()
-> *mut LeanObject {
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2974_ = lean_box(0);
    v___x_2975_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4;
    v___x_2976_ = l_Lean_mkConst(v___x_2975_, v___x_2974_);
    return v___x_2976_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9()
-> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2982_ = lean_box(0);
    v___x_2983_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8;
    v___x_2984_ = l_Lean_mkConst(v___x_2983_, v___x_2982_);
    return v___x_2984_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12()
-> *mut LeanObject {
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    v___x_2989_ = lean_box(0);
    v___x_2990_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11;
    v___x_2991_ = l_Lean_mkConst(v___x_2990_, v___x_2989_);
    return v___x_2991_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13()
-> *mut LeanObject {
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    v___x_2992_ = lean_unsigned_to_nat(0);
    v___x_2993_ = l_Lean_mkNatLit(v___x_2992_);
    return v___x_2993_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17()
-> *mut LeanObject {
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    v___x_2999_ = lean_box(0);
    v___x_3000_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16;
    v___x_3001_ = l_Lean_mkConst(v___x_3000_, v___x_2999_);
    return v___x_3001_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(
    mut v_a_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3003_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
                v___x_3004_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3003_, v_a_3002_);
                v_fst_3005_ = lean_ctor_get(v___x_3004_, 0);
                lean_inc(v_fst_3005_);
                v_snd_3006_ = lean_ctor_get(v___x_3004_, 1);
                lean_inc(v_snd_3006_);
                lean_dec_ref(v___x_3004_);
                v___x_3007_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
                v___x_3008_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3007_, v_snd_3006_);
                v_fst_3009_ = lean_ctor_get(v___x_3008_, 0);
                lean_inc(v_fst_3009_);
                v_snd_3010_ = lean_ctor_get(v___x_3008_, 1);
                lean_inc(v_snd_3010_);
                lean_dec_ref(v___x_3008_);
                v___x_3011_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
                v___x_3012_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3011_, v_snd_3010_);
                v_fst_3013_ = lean_ctor_get(v___x_3012_, 0);
                lean_inc(v_fst_3013_);
                v_snd_3014_ = lean_ctor_get(v___x_3012_, 1);
                lean_inc(v_snd_3014_);
                lean_dec_ref(v___x_3012_);
                v___x_3015_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
                v___x_3016_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3015_, v_snd_3014_);
                v_fst_3017_ = lean_ctor_get(v___x_3016_, 0);
                lean_inc(v_fst_3017_);
                v_snd_3018_ = lean_ctor_get(v___x_3016_, 1);
                lean_inc(v_snd_3018_);
                lean_dec_ref(v___x_3016_);
                v___x_3019_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
                v___x_3020_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3019_, v_snd_3018_);
                v_fst_3021_ = lean_ctor_get(v___x_3020_, 0);
                lean_inc(v_fst_3021_);
                v_snd_3022_ = lean_ctor_get(v___x_3020_, 1);
                lean_inc(v_snd_3022_);
                lean_dec_ref(v___x_3020_);
                v___x_3023_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
                v___x_3024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3023_, v_snd_3022_);
                v_fst_3025_ = lean_ctor_get(v___x_3024_, 0);
                lean_inc(v_fst_3025_);
                v_snd_3026_ = lean_ctor_get(v___x_3024_, 1);
                lean_inc(v_snd_3026_);
                lean_dec_ref(v___x_3024_);
                v___x_3027_ = l_Lean_Int_mkType;
                v___x_3028_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3027_, v_snd_3026_);
                v_fst_3029_ = lean_ctor_get(v___x_3028_, 0);
                v_snd_3030_ = lean_ctor_get(v___x_3028_, 1);
                v_isSharedCheck_3038_ = (!lean_is_exclusive(v___x_3028_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v___x_3032_ = v___x_3028_;
                    v_isShared_3033_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3030_);
                    lean_inc(v_fst_3029_);
                    lean_dec(v___x_3028_);
                    v___x_3032_ = lean_box(0);
                    v_isShared_3033_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3034_ = lean_alloc_ctor(0, 7, (0) as u32);
                lean_ctor_set(v___x_3034_, 0, v_fst_3009_);
                lean_ctor_set(v___x_3034_, 1, v_fst_3005_);
                lean_ctor_set(v___x_3034_, 2, v_fst_3021_);
                lean_ctor_set(v___x_3034_, 3, v_fst_3017_);
                lean_ctor_set(v___x_3034_, 4, v_fst_3013_);
                lean_ctor_set(v___x_3034_, 5, v_fst_3025_);
                lean_ctor_set(v___x_3034_, 6, v_fst_3029_);
                if v_isShared_3033_ == 0 {
                    lean_ctor_set(v___x_3032_, 0, v___x_3034_);
                    v___x_3036_ = v___x_3032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_snd_3030_);
                    v___x_3036_ = v_reuseFailAlloc_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3039_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    v___x_3040_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once
        ),
        _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0,
    );
    v___x_3041_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3041_, 0, v___x_3040_);
    return v___x_3041_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(
    mut v_00_u03b2_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    v___x_3043_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once
        ),
        _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1,
    );
    return v___x_3043_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(
    mut v_opts_3044_: *mut LeanObject,
    mut v_opt_3045_: *mut LeanObject,
) -> u8 {
    let mut v_name_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    v_name_3046_ = lean_ctor_get(v_opt_3045_, 0);
    v_defValue_3047_ = lean_ctor_get(v_opt_3045_, 1);
    v_map_3048_ = lean_ctor_get(v_opts_3044_, 0);
    v___x_3049_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3048_,
            v_name_3046_,
        );
    if lean_obj_tag(v___x_3049_) == 0 {
        let mut v___x_3050_: u8 = 0;
        v___x_3050_ = (lean_unbox(v_defValue_3047_) as u8);
        return v___x_3050_;
    } else {
        let mut v_val_3051_: *mut LeanObject = core::ptr::null_mut();
        v_val_3051_ = lean_ctor_get(v___x_3049_, 0);
        lean_inc(v_val_3051_);
        lean_dec_ref_known(v___x_3049_, 1);
        if lean_obj_tag(v_val_3051_) == 1 {
            let mut v_v_3052_: u8 = 0;
            v_v_3052_ = lean_ctor_get_uint8(v_val_3051_, 0 as u32);
            lean_dec_ref_known(v_val_3051_, 0);
            return v_v_3052_;
        } else {
            let mut v___x_3053_: u8 = 0;
            lean_dec(v_val_3051_);
            v___x_3053_ = (lean_unbox(v_defValue_3047_) as u8);
            return v___x_3053_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(
    mut v_opts_3054_: *mut LeanObject,
    mut v_opt_3055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3056_ =
        l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_opts_3054_, v_opt_3055_);
    lean_dec_ref(v_opt_3055_);
    lean_dec_ref(v_opts_3054_);
    v_r_3057_ = lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3058_ =
        l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(lean_box(0));
    return v___x_3058_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    v___x_3059_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3059_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    v___x_3060_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1,
    );
    v___x_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3061_, 0, v___x_3060_);
    return v___x_3061_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    v___x_3062_ = lean_box(0);
    v___x_3063_ = lean_unsigned_to_nat(16);
    v___x_3064_ = lean_mk_array(v___x_3063_, v___x_3062_);
    return v___x_3064_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    v___x_3065_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3,
    );
    v___x_3066_ = lean_unsigned_to_nat(0);
    v___x_3067_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3067_, 0, v___x_3066_);
    lean_ctor_set(v___x_3067_, 1, v___x_3065_);
    return v___x_3067_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    v___x_3068_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4,
    );
    v___x_3069_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3069_, 0, v___x_3068_);
    lean_ctor_set(v___x_3069_, 1, v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run___redArg(
    mut v_x_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3104_: u8 = 0;
    let mut v_a_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v_ref_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                v___x_3077_ =
                    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_3076_);
                v_fst_3078_ = lean_ctor_get(v___x_3077_, 0);
                v_snd_3079_ = lean_ctor_get(v___x_3077_, 1);
                v_isSharedCheck_3120_ = (!lean_is_exclusive(v___x_3077_)) as u8;
                if v_isSharedCheck_3120_ == 0 {
                    v___x_3081_ = v___x_3077_;
                    v_isShared_3082_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3079_);
                    lean_inc(v_fst_3078_);
                    lean_dec(v___x_3077_);
                    v___x_3081_ = lean_box(0);
                    v_isShared_3082_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3083_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
                if lean_obj_tag(v___x_3083_) == 0 {
                    lean_del_object(v___x_3081_);
                    v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
                    lean_inc(v_a_3084_);
                    lean_dec_ref_known(v___x_3083_, 1);
                    v_options_3085_ = lean_ctor_get(v_a_3073_, 2);
                    v___x_3086_ = l_Lean_Meta_Sym_sym_debug;
                    v___x_3087_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(
                        v_options_3085_,
                        v___x_3086_,
                    );
                    v___x_3088_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2,
                    );
                    v___x_3089_ = lean_box(0);
                    v___x_3090_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5,
                    );
                    v___x_3091_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_3091_, 0, v_snd_3079_);
                    lean_ctor_set(v___x_3091_, 1, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 2, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 3, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 4, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 5, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 6, v___x_3088_);
                    lean_ctor_set(v___x_3091_, 7, v_a_3084_);
                    lean_ctor_set(v___x_3091_, 8, v___x_3089_);
                    lean_ctor_set(v___x_3091_, 9, v___x_3090_);
                    lean_ctor_set_uint8(
                        v___x_3091_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v___x_3087_,
                    );
                    v___x_3092_ = lean_st_mk_ref(v___x_3091_);
                    v___x_3093_ = 1;
                    v___x_3094_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3094_, 0, v_fst_3078_);
                    lean_ctor_set_uint8(
                        v___x_3094_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3093_,
                    );
                    lean_inc(v_a_3074_);
                    lean_inc_ref(v_a_3073_);
                    lean_inc(v_a_3072_);
                    lean_inc_ref(v_a_3071_);
                    lean_inc(v___x_3092_);
                    v___x_3095_ = lean_apply_7(
                        v_x_3070_,
                        v___x_3094_,
                        v___x_3092_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3095_) == 0 {
                        v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
                        v_isSharedCheck_3104_ = (!lean_is_exclusive(v___x_3095_)) as u8;
                        if v_isSharedCheck_3104_ == 0 {
                            v___x_3098_ = v___x_3095_;
                            v_isShared_3099_ = v_isSharedCheck_3104_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3096_);
                            lean_dec(v___x_3095_);
                            v___x_3098_ = lean_box(0);
                            v_isShared_3099_ = v_isSharedCheck_3104_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3092_);
                        return v___x_3095_;
                    }
                } else {
                    lean_dec(v_snd_3079_);
                    lean_dec(v_fst_3078_);
                    lean_dec_ref(v_x_3070_);
                    v_a_3105_ = lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3119_ = (!lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3107_ = v___x_3083_;
                        v_isShared_3108_ = v_isSharedCheck_3119_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3105_);
                        lean_dec(v___x_3083_);
                        v___x_3107_ = lean_box(0);
                        v_isShared_3108_ = v_isSharedCheck_3119_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3100_ = lean_st_ref_get(v___x_3092_);
                lean_dec(v___x_3092_);
                lean_dec(v___x_3100_);
                if v_isShared_3099_ == 0 {
                    v___x_3102_ = v___x_3098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3096_);
                    v___x_3102_ = v_reuseFailAlloc_3103_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3102_;
            }
            4 => {
                v_ref_3109_ = lean_ctor_get(v_a_3073_, 5);
                v___x_3110_ = lean_io_error_to_string(v_a_3105_);
                v___x_3111_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3111_, 0, v___x_3110_);
                v___x_3112_ = l_Lean_MessageData_ofFormat(v___x_3111_);
                lean_inc(v_ref_3109_);
                if v_isShared_3082_ == 0 {
                    lean_ctor_set(v___x_3081_, 1, v___x_3112_);
                    lean_ctor_set(v___x_3081_, 0, v_ref_3109_);
                    v___x_3114_ = v___x_3081_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_ref_3109_);
                    lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3118_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3108_ == 0 {
                    lean_ctor_set(v___x_3107_, 0, v___x_3114_);
                    v___x_3116_ = v___x_3107_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
                    v___x_3116_ = v_reuseFailAlloc_3117_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run___redArg___boxed(
    mut v_x_3121_: *mut LeanObject,
    mut v_a_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v_a_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3127_: *mut LeanObject = core::ptr::null_mut();
    v_res_3127_ =
        l_Lean_Meta_Sym_SymM_run___redArg(v_x_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
    lean_dec(v_a_3125_);
    lean_dec_ref(v_a_3124_);
    lean_dec(v_a_3123_);
    lean_dec_ref(v_a_3122_);
    return v_res_3127_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run(
    mut v_00_u03b1_3128_: *mut LeanObject,
    mut v_x_3129_: *mut LeanObject,
    mut v_a_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
    mut v_a_3132_: *mut LeanObject,
    mut v_a_3133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    v___x_3135_ =
        l_Lean_Meta_Sym_SymM_run___redArg(v_x_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
    return v___x_3135_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run___boxed(
    mut v_00_u03b1_3136_: *mut LeanObject,
    mut v_x_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
    mut v_a_3139_: *mut LeanObject,
    mut v_a_3140_: *mut LeanObject,
    mut v_a_3141_: *mut LeanObject,
    mut v_a_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3143_: *mut LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Meta_Sym_SymM_run(
        v_00_u03b1_3136_,
        v_x_3137_,
        v_a_3138_,
        v_a_3139_,
        v_a_3140_,
        v_a_3141_,
    );
    lean_dec(v_a_3141_);
    lean_dec_ref(v_a_3140_);
    lean_dec(v_a_3139_);
    lean_dec_ref(v_a_3138_);
    return v_res_3143_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___redArg(
    mut v_a_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sharedExprs_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    v_sharedExprs_3146_ = lean_ctor_get(v_a_3144_, 0);
    lean_inc_ref(v_sharedExprs_3146_);
    v___x_3147_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3147_, 0, v_sharedExprs_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3150_: *mut LeanObject = core::ptr::null_mut();
    v_res_3150_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3148_);
    lean_dec_ref(v_a_3148_);
    return v_res_3150_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs(
    mut v_a_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3151_);
    return v___x_3158_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___boxed(
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Lean_Meta_Sym_getSharedExprs(
        v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_,
    );
    lean_dec(v_a_3164_);
    lean_dec_ref(v_a_3163_);
    lean_dec(v_a_3162_);
    lean_dec_ref(v_a_3161_);
    lean_dec(v_a_3160_);
    lean_dec_ref(v_a_3159_);
    return v_res_3166_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr___redArg(
    mut v_a_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v_trueExpr_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3167_);
                v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
                v_isSharedCheck_3178_ = (!lean_is_exclusive(v___x_3169_)) as u8;
                if v_isSharedCheck_3178_ == 0 {
                    v___x_3172_ = v___x_3169_;
                    v_isShared_3173_ = v_isSharedCheck_3178_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3170_);
                    lean_dec(v___x_3169_);
                    v___x_3172_ = lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3178_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trueExpr_3174_ = lean_ctor_get(v_a_3170_, 0);
                lean_inc_ref(v_trueExpr_3174_);
                lean_dec(v_a_3170_);
                if v_isShared_3173_ == 0 {
                    lean_ctor_set(v___x_3172_, 0, v_trueExpr_3174_);
                    v___x_3176_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_trueExpr_3174_);
                    v___x_3176_ = v_reuseFailAlloc_3177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr___redArg___boxed(
    mut v_a_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3181_: *mut LeanObject = core::ptr::null_mut();
    v_res_3181_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3179_);
    lean_dec_ref(v_a_3179_);
    return v_res_3181_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr(
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3182_);
    return v___x_3189_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr___boxed(
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
    mut v_a_3192_: *mut LeanObject,
    mut v_a_3193_: *mut LeanObject,
    mut v_a_3194_: *mut LeanObject,
    mut v_a_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3197_: *mut LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Lean_Meta_Sym_getTrueExpr(
        v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_,
    );
    lean_dec(v_a_3195_);
    lean_dec_ref(v_a_3194_);
    lean_dec(v_a_3193_);
    lean_dec_ref(v_a_3192_);
    lean_dec(v_a_3191_);
    lean_dec_ref(v_a_3190_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr___redArg(
    mut v_e_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v_a_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3201_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3199_);
                if lean_obj_tag(v___x_3201_) == 0 {
                    v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3211_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3211_ == 0 {
                        v___x_3204_ = v___x_3201_;
                        v_isShared_3205_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3202_);
                        lean_dec(v___x_3201_);
                        v___x_3204_ = lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3212_ = lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3219_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v___x_3214_ = v___x_3201_;
                        v_isShared_3215_ = v_isSharedCheck_3219_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3212_);
                        lean_dec(v___x_3201_);
                        v___x_3214_ = lean_box(0);
                        v_isShared_3215_ = v_isSharedCheck_3219_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3206_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_3198_, v_a_3202_,
                    );
                lean_dec(v_a_3202_);
                v___x_3207_ = lean_box((v___x_3206_) as usize);
                if v_isShared_3205_ == 0 {
                    lean_ctor_set(v___x_3204_, 0, v___x_3207_);
                    v___x_3209_ = v___x_3204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
                    v___x_3209_ = v_reuseFailAlloc_3210_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3209_;
            }
            3 => {
                if v_isShared_3215_ == 0 {
                    v___x_3217_ = v___x_3214_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
                    v___x_3217_ = v_reuseFailAlloc_3218_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr___redArg___boxed(
    mut v_e_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_3220_, v_a_3221_);
    lean_dec_ref(v_a_3221_);
    lean_dec_ref(v_e_3220_);
    return v_res_3223_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr(
    mut v_e_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    v___x_3232_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_3224_, v_a_3225_);
    return v___x_3232_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr___boxed(
    mut v_e_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
    mut v_a_3240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3241_: *mut LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_Meta_Sym_isTrueExpr(
        v_e_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_,
    );
    lean_dec(v_a_3239_);
    lean_dec_ref(v_a_3238_);
    lean_dec(v_a_3237_);
    lean_dec_ref(v_a_3236_);
    lean_dec(v_a_3235_);
    lean_dec_ref(v_a_3234_);
    lean_dec_ref(v_e_3233_);
    return v_res_3241_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr___redArg(
    mut v_a_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v_falseExpr_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3244_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3242_);
                v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
                v_isSharedCheck_3253_ = (!lean_is_exclusive(v___x_3244_)) as u8;
                if v_isSharedCheck_3253_ == 0 {
                    v___x_3247_ = v___x_3244_;
                    v_isShared_3248_ = v_isSharedCheck_3253_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3245_);
                    lean_dec(v___x_3244_);
                    v___x_3247_ = lean_box(0);
                    v_isShared_3248_ = v_isSharedCheck_3253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_falseExpr_3249_ = lean_ctor_get(v_a_3245_, 1);
                lean_inc_ref(v_falseExpr_3249_);
                lean_dec(v_a_3245_);
                if v_isShared_3248_ == 0 {
                    lean_ctor_set(v___x_3247_, 0, v_falseExpr_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_falseExpr_3249_);
                    v___x_3251_ = v_reuseFailAlloc_3252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr___redArg___boxed(
    mut v_a_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3256_: *mut LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3254_);
    lean_dec_ref(v_a_3254_);
    return v_res_3256_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr(
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    v___x_3264_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3257_);
    return v___x_3264_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr___boxed(
    mut v_a_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
    mut v_a_3267_: *mut LeanObject,
    mut v_a_3268_: *mut LeanObject,
    mut v_a_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3272_: *mut LeanObject = core::ptr::null_mut();
    v_res_3272_ = l_Lean_Meta_Sym_getFalseExpr(
        v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_,
    );
    lean_dec(v_a_3270_);
    lean_dec_ref(v_a_3269_);
    lean_dec(v_a_3268_);
    lean_dec_ref(v_a_3267_);
    lean_dec(v_a_3266_);
    lean_dec_ref(v_a_3265_);
    return v_res_3272_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr___redArg(
    mut v_e_3273_: *mut LeanObject,
    mut v_a_3274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3276_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3274_);
                if lean_obj_tag(v___x_3276_) == 0 {
                    v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
                    v_isSharedCheck_3286_ = (!lean_is_exclusive(v___x_3276_)) as u8;
                    if v_isSharedCheck_3286_ == 0 {
                        v___x_3279_ = v___x_3276_;
                        v_isShared_3280_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3277_);
                        lean_dec(v___x_3276_);
                        v___x_3279_ = lean_box(0);
                        v_isShared_3280_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3287_ = lean_ctor_get(v___x_3276_, 0);
                    v_isSharedCheck_3294_ = (!lean_is_exclusive(v___x_3276_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3276_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3287_);
                        lean_dec(v___x_3276_);
                        v___x_3289_ = lean_box(0);
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3281_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_3273_, v_a_3277_,
                    );
                lean_dec(v_a_3277_);
                v___x_3282_ = lean_box((v___x_3281_) as usize);
                if v_isShared_3280_ == 0 {
                    lean_ctor_set(v___x_3279_, 0, v___x_3282_);
                    v___x_3284_ = v___x_3279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3284_;
            }
            3 => {
                if v_isShared_3290_ == 0 {
                    v___x_3292_ = v___x_3289_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
                    v___x_3292_ = v_reuseFailAlloc_3293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr___redArg___boxed(
    mut v_e_3295_: *mut LeanObject,
    mut v_a_3296_: *mut LeanObject,
    mut v_a_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3298_: *mut LeanObject = core::ptr::null_mut();
    v_res_3298_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_3295_, v_a_3296_);
    lean_dec_ref(v_a_3296_);
    lean_dec_ref(v_e_3295_);
    return v_res_3298_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr(
    mut v_e_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    v___x_3307_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_3299_, v_a_3300_);
    return v___x_3307_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr___boxed(
    mut v_e_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
    mut v_a_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3316_: *mut LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Meta_Sym_isFalseExpr(
        v_e_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_,
    );
    lean_dec(v_a_3314_);
    lean_dec_ref(v_a_3313_);
    lean_dec(v_a_3312_);
    lean_dec_ref(v_a_3311_);
    lean_dec(v_a_3310_);
    lean_dec_ref(v_a_3309_);
    lean_dec_ref(v_e_3308_);
    return v_res_3316_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr___redArg(
    mut v_a_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v_btrueExpr_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3319_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3317_);
                v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
                v_isSharedCheck_3328_ = (!lean_is_exclusive(v___x_3319_)) as u8;
                if v_isSharedCheck_3328_ == 0 {
                    v___x_3322_ = v___x_3319_;
                    v_isShared_3323_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3320_);
                    lean_dec(v___x_3319_);
                    v___x_3322_ = lean_box(0);
                    v_isShared_3323_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_btrueExpr_3324_ = lean_ctor_get(v_a_3320_, 3);
                lean_inc_ref(v_btrueExpr_3324_);
                lean_dec(v_a_3320_);
                if v_isShared_3323_ == 0 {
                    lean_ctor_set(v___x_3322_, 0, v_btrueExpr_3324_);
                    v___x_3326_ = v___x_3322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_btrueExpr_3324_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr___redArg___boxed(
    mut v_a_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3329_);
    lean_dec_ref(v_a_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr(
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3332_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr___boxed(
    mut v_a_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3347_: *mut LeanObject = core::ptr::null_mut();
    v_res_3347_ = l_Lean_Meta_Sym_getBoolTrueExpr(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_,
    );
    lean_dec(v_a_3345_);
    lean_dec_ref(v_a_3344_);
    lean_dec(v_a_3343_);
    lean_dec_ref(v_a_3342_);
    lean_dec(v_a_3341_);
    lean_dec_ref(v_a_3340_);
    return v_res_3347_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr___redArg(
    mut v_e_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3361_: u8 = 0;
    let mut v_a_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3351_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3349_);
                if lean_obj_tag(v___x_3351_) == 0 {
                    v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
                    v_isSharedCheck_3361_ = (!lean_is_exclusive(v___x_3351_)) as u8;
                    if v_isSharedCheck_3361_ == 0 {
                        v___x_3354_ = v___x_3351_;
                        v_isShared_3355_ = v_isSharedCheck_3361_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3352_);
                        lean_dec(v___x_3351_);
                        v___x_3354_ = lean_box(0);
                        v_isShared_3355_ = v_isSharedCheck_3361_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3362_ = lean_ctor_get(v___x_3351_, 0);
                    v_isSharedCheck_3369_ = (!lean_is_exclusive(v___x_3351_)) as u8;
                    if v_isSharedCheck_3369_ == 0 {
                        v___x_3364_ = v___x_3351_;
                        v_isShared_3365_ = v_isSharedCheck_3369_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3362_);
                        lean_dec(v___x_3351_);
                        v___x_3364_ = lean_box(0);
                        v_isShared_3365_ = v_isSharedCheck_3369_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3356_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_3348_, v_a_3352_,
                    );
                lean_dec(v_a_3352_);
                v___x_3357_ = lean_box((v___x_3356_) as usize);
                if v_isShared_3355_ == 0 {
                    lean_ctor_set(v___x_3354_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
                    v___x_3359_ = v_reuseFailAlloc_3360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3359_;
            }
            3 => {
                if v_isShared_3365_ == 0 {
                    v___x_3367_ = v___x_3364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
                    v___x_3367_ = v_reuseFailAlloc_3368_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr___redArg___boxed(
    mut v_e_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
    mut v_a_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_3370_, v_a_3371_);
    lean_dec_ref(v_a_3371_);
    lean_dec_ref(v_e_3370_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr(
    mut v_e_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    v___x_3382_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_3374_, v_a_3375_);
    return v___x_3382_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr___boxed(
    mut v_e_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3391_: *mut LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Lean_Meta_Sym_isBoolTrueExpr(
        v_e_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_,
    );
    lean_dec(v_a_3389_);
    lean_dec_ref(v_a_3388_);
    lean_dec(v_a_3387_);
    lean_dec_ref(v_a_3386_);
    lean_dec(v_a_3385_);
    lean_dec_ref(v_a_3384_);
    lean_dec_ref(v_e_3383_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr___redArg(
    mut v_a_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v_bfalseExpr_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3394_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3392_);
                v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
                v_isSharedCheck_3403_ = (!lean_is_exclusive(v___x_3394_)) as u8;
                if v_isSharedCheck_3403_ == 0 {
                    v___x_3397_ = v___x_3394_;
                    v_isShared_3398_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3395_);
                    lean_dec(v___x_3394_);
                    v___x_3397_ = lean_box(0);
                    v_isShared_3398_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_bfalseExpr_3399_ = lean_ctor_get(v_a_3395_, 4);
                lean_inc_ref(v_bfalseExpr_3399_);
                lean_dec(v_a_3395_);
                if v_isShared_3398_ == 0 {
                    lean_ctor_set(v___x_3397_, 0, v_bfalseExpr_3399_);
                    v___x_3401_ = v___x_3397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_bfalseExpr_3399_);
                    v___x_3401_ = v_reuseFailAlloc_3402_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr___redArg___boxed(
    mut v_a_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3406_: *mut LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3404_);
    lean_dec_ref(v_a_3404_);
    return v_res_3406_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr(
    mut v_a_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
    mut v_a_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3407_);
    return v___x_3414_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr___boxed(
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3422_: *mut LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_Meta_Sym_getBoolFalseExpr(
        v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_,
    );
    lean_dec(v_a_3420_);
    lean_dec_ref(v_a_3419_);
    lean_dec(v_a_3418_);
    lean_dec_ref(v_a_3417_);
    lean_dec(v_a_3416_);
    lean_dec_ref(v_a_3415_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr___redArg(
    mut v_e_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_a_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3426_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3424_);
                if lean_obj_tag(v___x_3426_) == 0 {
                    v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
                    v_isSharedCheck_3436_ = (!lean_is_exclusive(v___x_3426_)) as u8;
                    if v_isSharedCheck_3436_ == 0 {
                        v___x_3429_ = v___x_3426_;
                        v_isShared_3430_ = v_isSharedCheck_3436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3427_);
                        lean_dec(v___x_3426_);
                        v___x_3429_ = lean_box(0);
                        v_isShared_3430_ = v_isSharedCheck_3436_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3437_ = lean_ctor_get(v___x_3426_, 0);
                    v_isSharedCheck_3444_ = (!lean_is_exclusive(v___x_3426_)) as u8;
                    if v_isSharedCheck_3444_ == 0 {
                        v___x_3439_ = v___x_3426_;
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3437_);
                        lean_dec(v___x_3426_);
                        v___x_3439_ = lean_box(0);
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3431_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_3423_, v_a_3427_,
                    );
                lean_dec(v_a_3427_);
                v___x_3432_ = lean_box((v___x_3431_) as usize);
                if v_isShared_3430_ == 0 {
                    lean_ctor_set(v___x_3429_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
                    v___x_3434_ = v_reuseFailAlloc_3435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3434_;
            }
            3 => {
                if v_isShared_3440_ == 0 {
                    v___x_3442_ = v___x_3439_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3442_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr___redArg___boxed(
    mut v_e_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_3445_, v_a_3446_);
    lean_dec_ref(v_a_3446_);
    lean_dec_ref(v_e_3445_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr(
    mut v_e_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
    mut v_a_3454_: *mut LeanObject,
    mut v_a_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    v___x_3457_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_3449_, v_a_3450_);
    return v___x_3457_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr___boxed(
    mut v_e_3458_: *mut LeanObject,
    mut v_a_3459_: *mut LeanObject,
    mut v_a_3460_: *mut LeanObject,
    mut v_a_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3466_: *mut LeanObject = core::ptr::null_mut();
    v_res_3466_ = l_Lean_Meta_Sym_isBoolFalseExpr(
        v_e_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_,
    );
    lean_dec(v_a_3464_);
    lean_dec_ref(v_a_3463_);
    lean_dec(v_a_3462_);
    lean_dec_ref(v_a_3461_);
    lean_dec(v_a_3460_);
    lean_dec_ref(v_a_3459_);
    lean_dec_ref(v_e_3458_);
    return v_res_3466_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr___redArg(
    mut v_a_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v_natZExpr_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3469_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3467_);
                v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
                v_isSharedCheck_3478_ = (!lean_is_exclusive(v___x_3469_)) as u8;
                if v_isSharedCheck_3478_ == 0 {
                    v___x_3472_ = v___x_3469_;
                    v_isShared_3473_ = v_isSharedCheck_3478_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3470_);
                    lean_dec(v___x_3469_);
                    v___x_3472_ = lean_box(0);
                    v_isShared_3473_ = v_isSharedCheck_3478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_natZExpr_3474_ = lean_ctor_get(v_a_3470_, 2);
                lean_inc_ref(v_natZExpr_3474_);
                lean_dec(v_a_3470_);
                if v_isShared_3473_ == 0 {
                    lean_ctor_set(v___x_3472_, 0, v_natZExpr_3474_);
                    v___x_3476_ = v___x_3472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_natZExpr_3474_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr___redArg___boxed(
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3481_: *mut LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_3479_);
    lean_dec_ref(v_a_3479_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr(
    mut v_a_3482_: *mut LeanObject,
    mut v_a_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
    mut v_a_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3489_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_3482_);
    return v___x_3489_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr___boxed(
    mut v_a_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3497_: *mut LeanObject = core::ptr::null_mut();
    v_res_3497_ = l_Lean_Meta_Sym_getNatZeroExpr(
        v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_,
    );
    lean_dec(v_a_3495_);
    lean_dec_ref(v_a_3494_);
    lean_dec(v_a_3493_);
    lean_dec_ref(v_a_3492_);
    lean_dec(v_a_3491_);
    lean_dec_ref(v_a_3490_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr___redArg(
    mut v_a_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v_ordEqExpr_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3500_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3498_);
                v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
                v_isSharedCheck_3509_ = (!lean_is_exclusive(v___x_3500_)) as u8;
                if v_isSharedCheck_3509_ == 0 {
                    v___x_3503_ = v___x_3500_;
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3501_);
                    lean_dec(v___x_3500_);
                    v___x_3503_ = lean_box(0);
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ordEqExpr_3505_ = lean_ctor_get(v_a_3501_, 5);
                lean_inc_ref(v_ordEqExpr_3505_);
                lean_dec(v_a_3501_);
                if v_isShared_3504_ == 0 {
                    lean_ctor_set(v___x_3503_, 0, v_ordEqExpr_3505_);
                    v___x_3507_ = v___x_3503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_ordEqExpr_3505_);
                    v___x_3507_ = v_reuseFailAlloc_3508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr___redArg___boxed(
    mut v_a_3510_: *mut LeanObject,
    mut v_a_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_3510_);
    lean_dec_ref(v_a_3510_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr(
    mut v_a_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
    mut v_a_3516_: *mut LeanObject,
    mut v_a_3517_: *mut LeanObject,
    mut v_a_3518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_3513_);
    return v___x_3520_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr___boxed(
    mut v_a_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3528_: *mut LeanObject = core::ptr::null_mut();
    v_res_3528_ = l_Lean_Meta_Sym_getOrderingEqExpr(
        v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_,
    );
    lean_dec(v_a_3526_);
    lean_dec_ref(v_a_3525_);
    lean_dec(v_a_3524_);
    lean_dec_ref(v_a_3523_);
    lean_dec(v_a_3522_);
    lean_dec_ref(v_a_3521_);
    return v_res_3528_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr___redArg(
    mut v_a_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v_intExpr_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3531_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3529_);
                v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
                v_isSharedCheck_3540_ = (!lean_is_exclusive(v___x_3531_)) as u8;
                if v_isSharedCheck_3540_ == 0 {
                    v___x_3534_ = v___x_3531_;
                    v_isShared_3535_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3532_);
                    lean_dec(v___x_3531_);
                    v___x_3534_ = lean_box(0);
                    v_isShared_3535_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_intExpr_3536_ = lean_ctor_get(v_a_3532_, 6);
                lean_inc_ref(v_intExpr_3536_);
                lean_dec(v_a_3532_);
                if v_isShared_3535_ == 0 {
                    lean_ctor_set(v___x_3534_, 0, v_intExpr_3536_);
                    v___x_3538_ = v___x_3534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_intExpr_3536_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr___redArg___boxed(
    mut v_a_3541_: *mut LeanObject,
    mut v_a_3542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3543_: *mut LeanObject = core::ptr::null_mut();
    v_res_3543_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_3541_);
    lean_dec_ref(v_a_3541_);
    return v_res_3543_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr(
    mut v_a_3544_: *mut LeanObject,
    mut v_a_3545_: *mut LeanObject,
    mut v_a_3546_: *mut LeanObject,
    mut v_a_3547_: *mut LeanObject,
    mut v_a_3548_: *mut LeanObject,
    mut v_a_3549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_3544_);
    return v___x_3551_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr___boxed(
    mut v_a_3552_: *mut LeanObject,
    mut v_a_3553_: *mut LeanObject,
    mut v_a_3554_: *mut LeanObject,
    mut v_a_3555_: *mut LeanObject,
    mut v_a_3556_: *mut LeanObject,
    mut v_a_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_Meta_Sym_getIntExpr(
        v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_,
    );
    lean_dec(v_a_3557_);
    lean_dec_ref(v_a_3556_);
    lean_dec(v_a_3555_);
    lean_dec_ref(v_a_3554_);
    lean_dec(v_a_3553_);
    lean_dec_ref(v_a_3552_);
    return v_res_3559_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3560_: *mut LeanObject,
    mut v_vals_3561_: *mut LeanObject,
    mut v_i_3562_: *mut LeanObject,
    mut v_k_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_array_get_size(v_keys_3560_);
                v___x_3565_ = lean_nat_dec_lt(v_i_3562_, v___x_3564_);
                if v___x_3565_ == 0 {
                    lean_dec_ref(v_k_3563_);
                    lean_dec(v_i_3562_);
                    v___x_3566_ = lean_box(0);
                    return v___x_3566_;
                } else {
                    v_k_x27_3567_ = lean_array_fget_borrowed(v_keys_3560_, v_i_3562_);
                    lean_inc(v_k_x27_3567_);
                    lean_inc_ref(v_k_3563_);
                    v___x_3568_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_3563_,
                            v_k_x27_3567_,
                        );
                    if v___x_3568_ == 0 {
                        v___x_3569_ = lean_unsigned_to_nat(1);
                        v___x_3570_ = lean_nat_add(v_i_3562_, v___x_3569_);
                        lean_dec(v_i_3562_);
                        v_i_3562_ = v___x_3570_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_3563_);
                        v___x_3572_ = lean_array_fget_borrowed(v_vals_3561_, v_i_3562_);
                        lean_dec(v_i_3562_);
                        lean_inc(v___x_3572_);
                        lean_inc(v_k_x27_3567_);
                        v___x_3573_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3573_, 0, v_k_x27_3567_);
                        lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                        v___x_3574_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3574_, 0, v___x_3573_);
                        return v___x_3574_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3575_: *mut LeanObject,
    mut v_vals_3576_: *mut LeanObject,
    mut v_i_3577_: *mut LeanObject,
    mut v_k_3578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3579_: *mut LeanObject = core::ptr::null_mut();
    v_res_3579_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_3575_, v_vals_3576_, v_i_3577_, v_k_3578_);
    lean_dec_ref(v_vals_3576_);
    lean_dec_ref(v_keys_3575_);
    return v_res_3579_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3580_: usize = 0;
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: usize = 0;
    v___x_3580_ = 5usize;
    v___x_3581_ = 1usize;
    v___x_3582_ = lean_usize_shift_left(v___x_3581_, v___x_3580_);
    return v___x_3582_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3583_: usize = 0;
    let mut v___x_3584_: usize = 0;
    let mut v___x_3585_: usize = 0;
    v___x_3583_ = 1usize;
    v___x_3584_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0);
    v___x_3585_ = lean_usize_sub(v___x_3584_, v___x_3583_);
    return v___x_3585_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(
    mut v_x_3586_: *mut LeanObject,
    mut v_x_3587_: usize,
    mut v_x_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: usize = 0;
    let mut v_j_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3586_) == 0 {
                    v_es_3589_ = lean_ctor_get(v_x_3586_, 0);
                    lean_inc_ref(v_es_3589_);
                    lean_dec_ref_known(v_x_3586_, 1);
                    v___x_3590_ = lean_box(2);
                    v___x_3591_ = 5usize;
                    v___x_3592_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_3593_ = lean_usize_land(v_x_3587_, v___x_3592_);
                    v_j_3594_ = lean_usize_to_nat(v___x_3593_);
                    v___x_3595_ = lean_array_get(v___x_3590_, v_es_3589_, v_j_3594_);
                    lean_dec(v_j_3594_);
                    lean_dec_ref(v_es_3589_);
                    match lean_obj_tag(v___x_3595_) {
                        0 => {
                            v_key_3596_ = lean_ctor_get(v___x_3595_, 0);
                            lean_inc_n(v_key_3596_, 2);
                            v_val_3597_ = lean_ctor_get(v___x_3595_, 1);
                            lean_inc(v_val_3597_);
                            lean_dec_ref_known(v___x_3595_, 2);
                            v___x_3598_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_3588_,
                                    v_key_3596_,
                                );
                            if v___x_3598_ == 0 {
                                lean_dec(v_val_3597_);
                                lean_dec(v_key_3596_);
                                v___x_3599_ = lean_box(0);
                                return v___x_3599_;
                            } else {
                                v___x_3600_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3600_, 0, v_key_3596_);
                                lean_ctor_set(v___x_3600_, 1, v_val_3597_);
                                v___x_3601_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3601_, 0, v___x_3600_);
                                return v___x_3601_;
                            }
                        }
                        1 => {
                            v_node_3602_ = lean_ctor_get(v___x_3595_, 0);
                            lean_inc(v_node_3602_);
                            lean_dec_ref_known(v___x_3595_, 1);
                            v___x_3603_ = lean_usize_shift_right(v_x_3587_, v___x_3591_);
                            v_x_3586_ = v_node_3602_;
                            v_x_3587_ = v___x_3603_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_x_3588_);
                            v___x_3605_ = lean_box(0);
                            return v___x_3605_;
                        }
                    }
                } else {
                    v_ks_3606_ = lean_ctor_get(v_x_3586_, 0);
                    lean_inc_ref(v_ks_3606_);
                    v_vs_3607_ = lean_ctor_get(v_x_3586_, 1);
                    lean_inc_ref(v_vs_3607_);
                    lean_dec_ref_known(v_x_3586_, 2);
                    v___x_3608_ = lean_unsigned_to_nat(0);
                    v___x_3609_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_ks_3606_, v_vs_3607_, v___x_3608_, v_x_3588_);
                    lean_dec_ref(v_vs_3607_);
                    lean_dec_ref(v_ks_3606_);
                    return v___x_3609_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(
    mut v_x_3610_: *mut LeanObject,
    mut v_x_3611_: *mut LeanObject,
    mut v_x_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2093__boxed_3613_: usize = 0;
    let mut v_res_3614_: *mut LeanObject = core::ptr::null_mut();
    v_x_2093__boxed_3613_ = lean_unbox_usize(v_x_3611_);
    lean_dec(v_x_3611_);
    v_res_3614_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3610_, v_x_2093__boxed_3613_, v_x_3612_);
    return v_res_3614_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
    mut v_x_3615_: *mut LeanObject,
    mut v_x_3616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3617_: u64 = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    v___x_3617_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3616_);
    v___x_3618_ = lean_uint64_to_usize(v___x_3617_);
    lean_inc_ref(v_x_3615_);
    v___x_3619_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3615_, v___x_3618_, v_x_3616_);
    return v___x_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg___boxed(
    mut v_x_3620_: *mut LeanObject,
    mut v_x_3621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3622_: *mut LeanObject = core::ptr::null_mut();
    v_res_3622_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
            v_x_3620_, v_x_3621_,
        );
    lean_dec_ref(v_x_3620_);
    return v_res_3622_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___redArg(
    mut v_e_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3637_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3658_: u8 = 0;
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_unused_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3626_ = lean_st_ref_take(v_a_3624_);
                v_share_3627_ = lean_ctor_get(v___x_3626_, 0);
                v_maxFVar_3628_ = lean_ctor_get(v___x_3626_, 1);
                v_proofInstInfo_3629_ = lean_ctor_get(v___x_3626_, 2);
                v_inferType_3630_ = lean_ctor_get(v___x_3626_, 3);
                v_getLevel_3631_ = lean_ctor_get(v___x_3626_, 4);
                v_congrInfo_3632_ = lean_ctor_get(v___x_3626_, 5);
                v_defEqI_3633_ = lean_ctor_get(v___x_3626_, 6);
                v_extensions_3634_ = lean_ctor_get(v___x_3626_, 7);
                v_issues_3635_ = lean_ctor_get(v___x_3626_, 8);
                v_canon_3636_ = lean_ctor_get(v___x_3626_, 9);
                v_debug_3637_ = lean_ctor_get_uint8(
                    v___x_3626_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3679_ = (!lean_is_exclusive(v___x_3626_)) as u8;
                if v_isSharedCheck_3679_ == 0 {
                    v___x_3639_ = v___x_3626_;
                    v_isShared_3640_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_3636_);
                    lean_inc(v_issues_3635_);
                    lean_inc(v_extensions_3634_);
                    lean_inc(v_defEqI_3633_);
                    lean_inc(v_congrInfo_3632_);
                    lean_inc(v_getLevel_3631_);
                    lean_inc(v_inferType_3630_);
                    lean_inc(v_proofInstInfo_3629_);
                    lean_inc(v_maxFVar_3628_);
                    lean_inc(v_share_3627_);
                    lean_dec(v___x_3626_);
                    v___x_3639_ = lean_box(0);
                    v_isShared_3640_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3641_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                if v_isShared_3640_ == 0 {
                    lean_ctor_set(v___x_3639_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3641_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_maxFVar_3628_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_proofInstInfo_3629_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 3, v_inferType_3630_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 4, v_getLevel_3631_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 5, v_congrInfo_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 6, v_defEqI_3633_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 7, v_extensions_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 8, v_issues_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 9, v_canon_3636_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3678_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_3637_,
                    );
                    v___x_3643_ = v_reuseFailAlloc_3678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3644_ = lean_st_ref_set(v_a_3624_, v___x_3643_);
                lean_inc_ref(v_e_3623_);
                v___x_3669_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_share_3627_, v_e_3623_);
                if lean_obj_tag(v___x_3669_) == 0 {
                    v___x_3670_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4,
                    );
                    v___x_3671_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3671_, 0, v___x_3670_);
                    lean_ctor_set(v___x_3671_, 1, v_share_3627_);
                    v___x_3672_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                        v_e_3623_,
                        v___x_3671_,
                    );
                    v_snd_3673_ = lean_ctor_get(v___x_3672_, 1);
                    lean_inc(v_snd_3673_);
                    v_fst_3674_ = lean_ctor_get(v___x_3672_, 0);
                    lean_inc(v_fst_3674_);
                    lean_dec_ref(v___x_3672_);
                    v_set_3675_ = lean_ctor_get(v_snd_3673_, 1);
                    lean_inc_ref(v_set_3675_);
                    lean_dec(v_snd_3673_);
                    v_fst_3646_ = v_fst_3674_;
                    v_snd_3647_ = v_set_3675_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v_e_3623_);
                    v_val_3676_ = lean_ctor_get(v___x_3669_, 0);
                    lean_inc(v_val_3676_);
                    lean_dec_ref_known(v___x_3669_, 1);
                    v_fst_3677_ = lean_ctor_get(v_val_3676_, 0);
                    lean_inc(v_fst_3677_);
                    lean_dec(v_val_3676_);
                    v_fst_3646_ = v_fst_3677_;
                    v_snd_3647_ = v_share_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3648_ = lean_st_ref_take(v_a_3624_);
                v_maxFVar_3649_ = lean_ctor_get(v___x_3648_, 1);
                v_proofInstInfo_3650_ = lean_ctor_get(v___x_3648_, 2);
                v_inferType_3651_ = lean_ctor_get(v___x_3648_, 3);
                v_getLevel_3652_ = lean_ctor_get(v___x_3648_, 4);
                v_congrInfo_3653_ = lean_ctor_get(v___x_3648_, 5);
                v_defEqI_3654_ = lean_ctor_get(v___x_3648_, 6);
                v_extensions_3655_ = lean_ctor_get(v___x_3648_, 7);
                v_issues_3656_ = lean_ctor_get(v___x_3648_, 8);
                v_canon_3657_ = lean_ctor_get(v___x_3648_, 9);
                v_debug_3658_ = lean_ctor_get_uint8(
                    v___x_3648_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3667_ = (!lean_is_exclusive(v___x_3648_)) as u8;
                if v_isSharedCheck_3667_ == 0 {
                    v_unused_3668_ = lean_ctor_get(v___x_3648_, 0);
                    lean_dec(v_unused_3668_);
                    v___x_3660_ = v___x_3648_;
                    v_isShared_3661_ = v_isSharedCheck_3667_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_3657_);
                    lean_inc(v_issues_3656_);
                    lean_inc(v_extensions_3655_);
                    lean_inc(v_defEqI_3654_);
                    lean_inc(v_congrInfo_3653_);
                    lean_inc(v_getLevel_3652_);
                    lean_inc(v_inferType_3651_);
                    lean_inc(v_proofInstInfo_3650_);
                    lean_inc(v_maxFVar_3649_);
                    lean_dec(v___x_3648_);
                    v___x_3660_ = lean_box(0);
                    v_isShared_3661_ = v_isSharedCheck_3667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3661_ == 0 {
                    lean_ctor_set(v___x_3660_, 0, v_snd_3647_);
                    v___x_3663_ = v___x_3660_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_snd_3647_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_maxFVar_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_proofInstInfo_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_inferType_3651_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_getLevel_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 5, v_congrInfo_3653_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 6, v_defEqI_3654_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 7, v_extensions_3655_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 8, v_issues_3656_);
                    lean_ctor_set(v_reuseFailAlloc_3666_, 9, v_canon_3657_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3666_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_3658_,
                    );
                    v___x_3663_ = v_reuseFailAlloc_3666_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3664_ = lean_st_ref_set(v_a_3624_, v___x_3663_);
                v___x_3665_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3665_, 0, v_fst_3646_);
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___redArg___boxed(
    mut v_e_3680_: *mut LeanObject,
    mut v_a_3681_: *mut LeanObject,
    mut v_a_3682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3683_: *mut LeanObject = core::ptr::null_mut();
    v_res_3683_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_3680_, v_a_3681_);
    lean_dec(v_a_3681_);
    return v_res_3683_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon(
    mut v_e_3684_: *mut LeanObject,
    mut v_a_3685_: *mut LeanObject,
    mut v_a_3686_: *mut LeanObject,
    mut v_a_3687_: *mut LeanObject,
    mut v_a_3688_: *mut LeanObject,
    mut v_a_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_3684_, v_a_3686_);
    return v___x_3692_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___boxed(
    mut v_e_3693_: *mut LeanObject,
    mut v_a_3694_: *mut LeanObject,
    mut v_a_3695_: *mut LeanObject,
    mut v_a_3696_: *mut LeanObject,
    mut v_a_3697_: *mut LeanObject,
    mut v_a_3698_: *mut LeanObject,
    mut v_a_3699_: *mut LeanObject,
    mut v_a_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3701_: *mut LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_Lean_Meta_Sym_shareCommon(
        v_e_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_,
    );
    lean_dec(v_a_3699_);
    lean_dec_ref(v_a_3698_);
    lean_dec(v_a_3697_);
    lean_dec_ref(v_a_3696_);
    lean_dec(v_a_3695_);
    lean_dec_ref(v_a_3694_);
    return v_res_3701_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(
    mut v_00_u03b2_3702_: *mut LeanObject,
    mut v_x_3703_: *mut LeanObject,
    mut v_x_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
            v_x_3703_, v_x_3704_,
        );
    return v___x_3705_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___boxed(
    mut v_00_u03b2_3706_: *mut LeanObject,
    mut v_x_3707_: *mut LeanObject,
    mut v_x_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(
        v_00_u03b2_3706_,
        v_x_3707_,
        v_x_3708_,
    );
    lean_dec_ref(v_x_3707_);
    return v_res_3709_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(
    mut v_00_u03b2_3710_: *mut LeanObject,
    mut v_x_3711_: *mut LeanObject,
    mut v_x_3712_: usize,
    mut v_x_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_3711_);
    v___x_3714_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3711_, v_x_3712_, v_x_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(
    mut v_00_u03b2_3715_: *mut LeanObject,
    mut v_x_3716_: *mut LeanObject,
    mut v_x_3717_: *mut LeanObject,
    mut v_x_3718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2255__boxed_3719_: usize = 0;
    let mut v_res_3720_: *mut LeanObject = core::ptr::null_mut();
    v_x_2255__boxed_3719_ = lean_unbox_usize(v_x_3717_);
    lean_dec(v_x_3717_);
    v_res_3720_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(v_00_u03b2_3715_, v_x_3716_, v_x_2255__boxed_3719_, v_x_3718_);
    lean_dec_ref(v_x_3716_);
    return v_res_3720_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3721_: *mut LeanObject,
    mut v_keys_3722_: *mut LeanObject,
    mut v_vals_3723_: *mut LeanObject,
    mut v_heq_3724_: *mut LeanObject,
    mut v_i_3725_: *mut LeanObject,
    mut v_k_3726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    v___x_3727_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_3722_, v_vals_3723_, v_i_3725_, v_k_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3728_: *mut LeanObject,
    mut v_keys_3729_: *mut LeanObject,
    mut v_vals_3730_: *mut LeanObject,
    mut v_heq_3731_: *mut LeanObject,
    mut v_i_3732_: *mut LeanObject,
    mut v_k_3733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3734_: *mut LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(v_00_u03b2_3728_, v_keys_3729_, v_vals_3730_, v_heq_3731_, v_i_3732_, v_k_3733_);
    lean_dec_ref(v_vals_3730_);
    lean_dec_ref(v_keys_3729_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___redArg(
    mut v_e_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3749_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3770_: u8 = 0;
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_unused_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3738_ = lean_st_ref_take(v_a_3736_);
                v_share_3739_ = lean_ctor_get(v___x_3738_, 0);
                v_maxFVar_3740_ = lean_ctor_get(v___x_3738_, 1);
                v_proofInstInfo_3741_ = lean_ctor_get(v___x_3738_, 2);
                v_inferType_3742_ = lean_ctor_get(v___x_3738_, 3);
                v_getLevel_3743_ = lean_ctor_get(v___x_3738_, 4);
                v_congrInfo_3744_ = lean_ctor_get(v___x_3738_, 5);
                v_defEqI_3745_ = lean_ctor_get(v___x_3738_, 6);
                v_extensions_3746_ = lean_ctor_get(v___x_3738_, 7);
                v_issues_3747_ = lean_ctor_get(v___x_3738_, 8);
                v_canon_3748_ = lean_ctor_get(v___x_3738_, 9);
                v_debug_3749_ = lean_ctor_get_uint8(
                    v___x_3738_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3782_ = (!lean_is_exclusive(v___x_3738_)) as u8;
                if v_isSharedCheck_3782_ == 0 {
                    v___x_3751_ = v___x_3738_;
                    v_isShared_3752_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_3748_);
                    lean_inc(v_issues_3747_);
                    lean_inc(v_extensions_3746_);
                    lean_inc(v_defEqI_3745_);
                    lean_inc(v_congrInfo_3744_);
                    lean_inc(v_getLevel_3743_);
                    lean_inc(v_inferType_3742_);
                    lean_inc(v_proofInstInfo_3741_);
                    lean_inc(v_maxFVar_3740_);
                    lean_inc(v_share_3739_);
                    lean_dec(v___x_3738_);
                    v___x_3751_ = lean_box(0);
                    v_isShared_3752_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3753_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                if v_isShared_3752_ == 0 {
                    lean_ctor_set(v___x_3751_, 0, v___x_3753_);
                    v___x_3755_ = v___x_3751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3753_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_maxFVar_3740_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_proofInstInfo_3741_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_inferType_3742_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_getLevel_3743_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 5, v_congrInfo_3744_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 6, v_defEqI_3745_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 7, v_extensions_3746_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 8, v_issues_3747_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 9, v_canon_3748_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3781_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_3749_,
                    );
                    v___x_3755_ = v_reuseFailAlloc_3781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3756_ = lean_st_ref_set(v_a_3736_, v___x_3755_);
                v___x_3757_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v_e_3735_, v_share_3739_);
                v_fst_3758_ = lean_ctor_get(v___x_3757_, 0);
                lean_inc(v_fst_3758_);
                v_snd_3759_ = lean_ctor_get(v___x_3757_, 1);
                lean_inc(v_snd_3759_);
                lean_dec_ref(v___x_3757_);
                v___x_3760_ = lean_st_ref_take(v_a_3736_);
                v_maxFVar_3761_ = lean_ctor_get(v___x_3760_, 1);
                v_proofInstInfo_3762_ = lean_ctor_get(v___x_3760_, 2);
                v_inferType_3763_ = lean_ctor_get(v___x_3760_, 3);
                v_getLevel_3764_ = lean_ctor_get(v___x_3760_, 4);
                v_congrInfo_3765_ = lean_ctor_get(v___x_3760_, 5);
                v_defEqI_3766_ = lean_ctor_get(v___x_3760_, 6);
                v_extensions_3767_ = lean_ctor_get(v___x_3760_, 7);
                v_issues_3768_ = lean_ctor_get(v___x_3760_, 8);
                v_canon_3769_ = lean_ctor_get(v___x_3760_, 9);
                v_debug_3770_ = lean_ctor_get_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3779_ = (!lean_is_exclusive(v___x_3760_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v_unused_3780_ = lean_ctor_get(v___x_3760_, 0);
                    lean_dec(v_unused_3780_);
                    v___x_3772_ = v___x_3760_;
                    v_isShared_3773_ = v_isSharedCheck_3779_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_3769_);
                    lean_inc(v_issues_3768_);
                    lean_inc(v_extensions_3767_);
                    lean_inc(v_defEqI_3766_);
                    lean_inc(v_congrInfo_3765_);
                    lean_inc(v_getLevel_3764_);
                    lean_inc(v_inferType_3763_);
                    lean_inc(v_proofInstInfo_3762_);
                    lean_inc(v_maxFVar_3761_);
                    lean_dec(v___x_3760_);
                    v___x_3772_ = lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3779_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3773_ == 0 {
                    lean_ctor_set(v___x_3772_, 0, v_snd_3759_);
                    v___x_3775_ = v___x_3772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_snd_3759_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_maxFVar_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_proofInstInfo_3762_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_inferType_3763_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_getLevel_3764_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_congrInfo_3765_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_defEqI_3766_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_extensions_3767_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_issues_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_canon_3769_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_3770_,
                    );
                    v___x_3775_ = v_reuseFailAlloc_3778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3776_ = lean_st_ref_set(v_a_3736_, v___x_3775_);
                v___x_3777_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3777_, 0, v_fst_3758_);
                return v___x_3777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(
    mut v_e_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3786_: *mut LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3783_, v_a_3784_);
    lean_dec(v_a_3784_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc(
    mut v_e_3787_: *mut LeanObject,
    mut v_a_3788_: *mut LeanObject,
    mut v_a_3789_: *mut LeanObject,
    mut v_a_3790_: *mut LeanObject,
    mut v_a_3791_: *mut LeanObject,
    mut v_a_3792_: *mut LeanObject,
    mut v_a_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    v___x_3795_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3787_, v_a_3789_);
    return v___x_3795_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___boxed(
    mut v_e_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
    mut v_a_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
    mut v_a_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3804_: *mut LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Lean_Meta_Sym_shareCommonInc(
        v_e_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_,
    );
    lean_dec(v_a_3802_);
    lean_dec_ref(v_a_3801_);
    lean_dec(v_a_3800_);
    lean_dec_ref(v_a_3799_);
    lean_dec(v_a_3798_);
    lean_dec_ref(v_a_3797_);
    return v_res_3804_;
}
pub unsafe fn l_Lean_Meta_Sym_share___redArg(
    mut v_e_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    v___x_3808_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3805_, v_a_3806_);
    return v___x_3808_;
}
pub unsafe fn l_Lean_Meta_Sym_share___redArg___boxed(
    mut v_e_3809_: *mut LeanObject,
    mut v_a_3810_: *mut LeanObject,
    mut v_a_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3812_: *mut LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Lean_Meta_Sym_share___redArg(v_e_3809_, v_a_3810_);
    lean_dec(v_a_3810_);
    return v_res_3812_;
}
pub unsafe fn l_Lean_Meta_Sym_share(
    mut v_e_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3813_, v_a_3815_);
    return v___x_3821_;
}
pub unsafe fn l_Lean_Meta_Sym_share___boxed(
    mut v_e_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
    mut v_a_3826_: *mut LeanObject,
    mut v_a_3827_: *mut LeanObject,
    mut v_a_3828_: *mut LeanObject,
    mut v_a_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3830_: *mut LeanObject = core::ptr::null_mut();
    v_res_3830_ = l_Lean_Meta_Sym_share(
        v_e_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_,
    );
    lean_dec(v_a_3828_);
    lean_dec_ref(v_a_3827_);
    lean_dec(v_a_3826_);
    lean_dec_ref(v_a_3825_);
    lean_dec(v_a_3824_);
    lean_dec_ref(v_a_3823_);
    return v_res_3830_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___redArg(
    mut v_a_3831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3834_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v___x_3833_ = lean_st_ref_get(v_a_3831_);
    v_debug_3834_ = lean_ctor_get_uint8(
        v___x_3833_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
    );
    lean_dec(v___x_3833_);
    v___x_3835_ = lean_box((v_debug_3834_) as usize);
    v___x_3836_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3836_, 0, v___x_3835_);
    return v___x_3836_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(
    mut v_a_3837_: *mut LeanObject,
    mut v_a_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3839_: *mut LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3837_);
    lean_dec(v_a_3837_);
    return v_res_3839_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled(
    mut v_a_3840_: *mut LeanObject,
    mut v_a_3841_: *mut LeanObject,
    mut v_a_3842_: *mut LeanObject,
    mut v_a_3843_: *mut LeanObject,
    mut v_a_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3848_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    v___x_3847_ = lean_st_ref_get(v_a_3841_);
    v_debug_3848_ = lean_ctor_get_uint8(
        v___x_3847_,
        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
    );
    lean_dec(v___x_3847_);
    v___x_3849_ = lean_box((v_debug_3848_) as usize);
    v___x_3850_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3850_, 0, v___x_3849_);
    return v___x_3850_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___boxed(
    mut v_a_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
    mut v_a_3854_: *mut LeanObject,
    mut v_a_3855_: *mut LeanObject,
    mut v_a_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3858_: *mut LeanObject = core::ptr::null_mut();
    v_res_3858_ = l_Lean_Meta_Sym_isDebugEnabled(
        v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_,
    );
    lean_dec(v_a_3856_);
    lean_dec_ref(v_a_3855_);
    lean_dec(v_a_3854_);
    lean_dec_ref(v_a_3853_);
    lean_dec(v_a_3852_);
    lean_dec_ref(v_a_3851_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___redArg(
    mut v_a_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_3861_: u8 = 0;
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    v_config_3861_ = lean_ctor_get_uint8(
        v_a_3859_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_3862_ = lean_box((v_config_3861_) as usize);
    v___x_3863_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3863_, 0, v___x_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___redArg___boxed(
    mut v_a_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3866_: *mut LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3864_);
    lean_dec_ref(v_a_3864_);
    return v_res_3866_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig(
    mut v_a_3867_: *mut LeanObject,
    mut v_a_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    v___x_3874_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3867_);
    return v___x_3874_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___boxed(
    mut v_a_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
    mut v_a_3877_: *mut LeanObject,
    mut v_a_3878_: *mut LeanObject,
    mut v_a_3879_: *mut LeanObject,
    mut v_a_3880_: *mut LeanObject,
    mut v_a_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3882_: *mut LeanObject = core::ptr::null_mut();
    v_res_3882_ = l_Lean_Meta_Sym_getConfig(
        v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_,
    );
    lean_dec(v_a_3880_);
    lean_dec_ref(v_a_3879_);
    lean_dec(v_a_3878_);
    lean_dec_ref(v_a_3877_);
    lean_dec(v_a_3876_);
    lean_dec_ref(v_a_3875_);
    return v_res_3882_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
    mut v_msgData_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
    mut v___y_3885_: *mut LeanObject,
    mut v___y_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    v___x_3889_ = lean_st_ref_get(v___y_3887_);
    v_env_3890_ = lean_ctor_get(v___x_3889_, 0);
    lean_inc_ref(v_env_3890_);
    lean_dec(v___x_3889_);
    v___x_3891_ = lean_st_ref_get(v___y_3885_);
    v_mctx_3892_ = lean_ctor_get(v___x_3891_, 0);
    lean_inc_ref(v_mctx_3892_);
    lean_dec(v___x_3891_);
    v_lctx_3893_ = lean_ctor_get(v___y_3884_, 2);
    v_options_3894_ = lean_ctor_get(v___y_3886_, 2);
    lean_inc_ref(v_options_3894_);
    lean_inc_ref(v_lctx_3893_);
    v___x_3895_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3895_, 0, v_env_3890_);
    lean_ctor_set(v___x_3895_, 1, v_mctx_3892_);
    lean_ctor_set(v___x_3895_, 2, v_lctx_3893_);
    lean_ctor_set(v___x_3895_, 3, v_options_3894_);
    v___x_3896_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3896_, 0, v___x_3895_);
    lean_ctor_set(v___x_3896_, 1, v_msgData_3883_);
    v___x_3897_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3897_, 0, v___x_3896_);
    return v___x_3897_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(
    mut v_msgData_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
    mut v___y_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
        v_msgData_3898_,
        v___y_3899_,
        v___y_3900_,
        v___y_3901_,
        v___y_3902_,
    );
    lean_dec(v___y_3902_);
    lean_dec_ref(v___y_3901_);
    lean_dec(v___y_3900_);
    lean_dec_ref(v___y_3899_);
    return v_res_3904_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: f64 = 0.0;
    v___x_3905_ = lean_unsigned_to_nat(0);
    v___x_3906_ = lean_float_of_nat(v___x_3905_);
    return v___x_3906_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
    mut v_cls_3910_: *mut LeanObject,
    mut v_msg_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v_tid_3936_: u64 = 0;
    let mut v_traces_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: f64 = 0.0;
    let mut v___x_3943_: u8 = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3917_ = lean_ctor_get(v___y_3914_, 5);
                v___x_3918_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
                        v_msg_3911_,
                        v___y_3912_,
                        v___y_3913_,
                        v___y_3914_,
                        v___y_3915_,
                    );
                v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                v_isSharedCheck_3963_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                if v_isSharedCheck_3963_ == 0 {
                    v___x_3921_ = v___x_3918_;
                    v_isShared_3922_ = v_isSharedCheck_3963_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3919_);
                    lean_dec(v___x_3918_);
                    v___x_3921_ = lean_box(0);
                    v_isShared_3922_ = v_isSharedCheck_3963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3923_ = lean_st_ref_take(v___y_3915_);
                v_traceState_3924_ = lean_ctor_get(v___x_3923_, 4);
                v_env_3925_ = lean_ctor_get(v___x_3923_, 0);
                v_nextMacroScope_3926_ = lean_ctor_get(v___x_3923_, 1);
                v_ngen_3927_ = lean_ctor_get(v___x_3923_, 2);
                v_auxDeclNGen_3928_ = lean_ctor_get(v___x_3923_, 3);
                v_cache_3929_ = lean_ctor_get(v___x_3923_, 5);
                v_messages_3930_ = lean_ctor_get(v___x_3923_, 6);
                v_infoState_3931_ = lean_ctor_get(v___x_3923_, 7);
                v_snapshotTasks_3932_ = lean_ctor_get(v___x_3923_, 8);
                v_isSharedCheck_3962_ = (!lean_is_exclusive(v___x_3923_)) as u8;
                if v_isSharedCheck_3962_ == 0 {
                    v___x_3934_ = v___x_3923_;
                    v_isShared_3935_ = v_isSharedCheck_3962_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3932_);
                    lean_inc(v_infoState_3931_);
                    lean_inc(v_messages_3930_);
                    lean_inc(v_cache_3929_);
                    lean_inc(v_traceState_3924_);
                    lean_inc(v_auxDeclNGen_3928_);
                    lean_inc(v_ngen_3927_);
                    lean_inc(v_nextMacroScope_3926_);
                    lean_inc(v_env_3925_);
                    lean_dec(v___x_3923_);
                    v___x_3934_ = lean_box(0);
                    v_isShared_3935_ = v_isSharedCheck_3962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3936_ = lean_ctor_get_uint64(
                    v_traceState_3924_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3937_ = lean_ctor_get(v_traceState_3924_, 0);
                v_isSharedCheck_3961_ = (!lean_is_exclusive(v_traceState_3924_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3939_ = v_traceState_3924_;
                    v_isShared_3940_ = v_isSharedCheck_3961_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3937_);
                    lean_dec(v_traceState_3924_);
                    v___x_3939_ = lean_box(0);
                    v_isShared_3940_ = v_isSharedCheck_3961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3941_ = lean_box(0);
                v___x_3942_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
                v___x_3943_ = 0;
                v___x_3944_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
                v___x_3945_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3945_, 0, v_cls_3910_);
                lean_ctor_set(v___x_3945_, 1, v___x_3941_);
                lean_ctor_set(v___x_3945_, 2, v___x_3944_);
                lean_ctor_set_float(
                    v___x_3945_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3942_,
                );
                lean_ctor_set_float(
                    v___x_3945_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3942_,
                );
                lean_ctor_set_uint8(
                    v___x_3945_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3943_,
                );
                v___x_3946_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2;
                v___x_3947_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3947_, 0, v___x_3945_);
                lean_ctor_set(v___x_3947_, 1, v_a_3919_);
                lean_ctor_set(v___x_3947_, 2, v___x_3946_);
                lean_inc(v_ref_3917_);
                v___x_3948_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v_ref_3917_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = l_Lean_PersistentArray_push___redArg(v_traces_3937_, v___x_3948_);
                if v_isShared_3940_ == 0 {
                    lean_ctor_set(v___x_3939_, 0, v___x_3949_);
                    v___x_3951_ = v___x_3939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3949_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3960_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3936_,
                    );
                    v___x_3951_ = v_reuseFailAlloc_3960_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3935_ == 0 {
                    lean_ctor_set(v___x_3934_, 4, v___x_3951_);
                    v___x_3953_ = v___x_3934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_env_3925_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_nextMacroScope_3926_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_ngen_3927_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_auxDeclNGen_3928_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 4, v___x_3951_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_cache_3929_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 6, v_messages_3930_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 7, v_infoState_3931_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 8, v_snapshotTasks_3932_);
                    v___x_3953_ = v_reuseFailAlloc_3959_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3954_ = lean_st_ref_set(v___y_3915_, v___x_3953_);
                v___x_3955_ = lean_box(0);
                if v_isShared_3922_ == 0 {
                    lean_ctor_set(v___x_3921_, 0, v___x_3955_);
                    v___x_3957_ = v___x_3921_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___boxed(
    mut v_cls_3964_: *mut LeanObject,
    mut v_msg_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3971_: *mut LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
        v_cls_3964_,
        v_msg_3965_,
        v___y_3966_,
        v___y_3967_,
        v___y_3968_,
        v___y_3969_,
    );
    lean_dec(v___y_3969_);
    lean_dec_ref(v___y_3968_);
    lean_dec(v___y_3967_);
    lean_dec_ref(v___y_3966_);
    return v_res_3971_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_reportIssue___closed__2() -> *mut LeanObject {
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: u8 = 0;
    let mut v___x_3977_: f64 = 0.0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
    v___x_3976_ = 1;
    v___x_3977_ = lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0,
    );
    v___x_3978_ = lean_box(0);
    v___x_3979_ = l_Lean_Meta_Sym_reportIssue___closed__1;
    v___x_3980_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_3980_, 0, v___x_3979_);
    lean_ctor_set(v___x_3980_, 1, v___x_3978_);
    lean_ctor_set(v___x_3980_, 2, v___x_3975_);
    lean_ctor_set_float(
        v___x_3980_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_3977_,
    );
    lean_ctor_set_float(
        v___x_3980_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_3977_,
    );
    lean_ctor_set_uint8(
        v___x_3980_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_3976_,
    );
    return v___x_3980_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_reportIssue___closed__5() -> *mut LeanObject {
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    v___x_3984_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_3985_ = l_Lean_Meta_Sym_reportIssue___closed__4;
    v___x_3986_ = l_Lean_Name_append(v___x_3985_, v___x_3984_);
    return v___x_3986_;
}
pub unsafe fn l_Lean_Meta_Sym_reportIssue(
    mut v_msg_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v_a_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4011_: u8 = 0;
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4023_: u8 = 0;
    let mut v_inheritedTraceOptions_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3998_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
                        v_msg_3987_,
                        v_a_3990_,
                        v_a_3991_,
                        v_a_3992_,
                        v_a_3993_,
                    );
                v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
                lean_inc(v_a_3999_);
                lean_dec_ref(v___x_3998_);
                v___x_4000_ = lean_st_ref_take(v_a_3989_);
                v_share_4001_ = lean_ctor_get(v___x_4000_, 0);
                v_maxFVar_4002_ = lean_ctor_get(v___x_4000_, 1);
                v_proofInstInfo_4003_ = lean_ctor_get(v___x_4000_, 2);
                v_inferType_4004_ = lean_ctor_get(v___x_4000_, 3);
                v_getLevel_4005_ = lean_ctor_get(v___x_4000_, 4);
                v_congrInfo_4006_ = lean_ctor_get(v___x_4000_, 5);
                v_defEqI_4007_ = lean_ctor_get(v___x_4000_, 6);
                v_extensions_4008_ = lean_ctor_get(v___x_4000_, 7);
                v_issues_4009_ = lean_ctor_get(v___x_4000_, 8);
                v_canon_4010_ = lean_ctor_get(v___x_4000_, 9);
                v_debug_4011_ = lean_ctor_get_uint8(
                    v___x_4000_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4030_ = (!lean_is_exclusive(v___x_4000_)) as u8;
                if v_isSharedCheck_4030_ == 0 {
                    v___x_4013_ = v___x_4000_;
                    v_isShared_4014_ = v_isSharedCheck_4030_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_canon_4010_);
                    lean_inc(v_issues_4009_);
                    lean_inc(v_extensions_4008_);
                    lean_inc(v_defEqI_4007_);
                    lean_inc(v_congrInfo_4006_);
                    lean_inc(v_getLevel_4005_);
                    lean_inc(v_inferType_4004_);
                    lean_inc(v_proofInstInfo_4003_);
                    lean_inc(v_maxFVar_4002_);
                    lean_inc(v_share_4001_);
                    lean_dec(v___x_4000_);
                    v___x_4013_ = lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4030_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3996_ = lean_box(0);
                v___x_3997_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3997_, 0, v___x_3996_);
                return v___x_3997_;
            }
            2 => {
                v___x_4015_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__2_once),
                    _init_l_Lean_Meta_Sym_reportIssue___closed__2,
                );
                v___x_4016_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2;
                lean_inc(v_a_3999_);
                v___x_4017_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4017_, 0, v___x_4015_);
                lean_ctor_set(v___x_4017_, 1, v_a_3999_);
                lean_ctor_set(v___x_4017_, 2, v___x_4016_);
                v___x_4018_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                lean_ctor_set(v___x_4018_, 1, v_issues_4009_);
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 8, v___x_4018_);
                    v___x_4020_ = v___x_4013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_share_4001_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_maxFVar_4002_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_proofInstInfo_4003_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 3, v_inferType_4004_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 4, v_getLevel_4005_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 5, v_congrInfo_4006_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 6, v_defEqI_4007_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 7, v_extensions_4008_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 8, v___x_4018_);
                    lean_ctor_set(v_reuseFailAlloc_4029_, 9, v_canon_4010_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4029_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4011_,
                    );
                    v___x_4020_ = v_reuseFailAlloc_4029_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4021_ = lean_st_ref_set(v_a_3989_, v___x_4020_);
                v_options_4022_ = lean_ctor_get(v_a_3992_, 2);
                v_hasTrace_4023_ = lean_ctor_get_uint8(
                    v_options_4022_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4023_ == 0 {
                    lean_dec(v_a_3999_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4024_ = lean_ctor_get(v_a_3992_, 13);
                    v___x_4025_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
                    v___x_4026_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__5_once),
                        _init_l_Lean_Meta_Sym_reportIssue___closed__5,
                    );
                    v___x_4027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4024_,
                        v_options_4022_,
                        v___x_4026_,
                    );
                    if v___x_4027_ == 0 {
                        lean_dec(v_a_3999_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4028_ =
                            l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
                                v___x_4025_,
                                v_a_3999_,
                                v_a_3990_,
                                v_a_3991_,
                                v_a_3992_,
                                v_a_3993_,
                            );
                        return v___x_4028_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_reportIssue___boxed(
    mut v_msg_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_a_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
    mut v_a_4036_: *mut LeanObject,
    mut v_a_4037_: *mut LeanObject,
    mut v_a_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4039_: *mut LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Lean_Meta_Sym_reportIssue(
        v_msg_4031_,
        v_a_4032_,
        v_a_4033_,
        v_a_4034_,
        v_a_4035_,
        v_a_4036_,
        v_a_4037_,
    );
    lean_dec(v_a_4037_);
    lean_dec_ref(v_a_4036_);
    lean_dec(v_a_4035_);
    lean_dec_ref(v_a_4034_);
    lean_dec(v_a_4033_);
    lean_dec_ref(v_a_4032_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(
    mut v_cls_4040_: *mut LeanObject,
    mut v_msg_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    v___x_4049_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
        v_cls_4040_,
        v_msg_4041_,
        v___y_4044_,
        v___y_4045_,
        v___y_4046_,
        v___y_4047_,
    );
    return v___x_4049_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___boxed(
    mut v_cls_4050_: *mut LeanObject,
    mut v_msg_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
    mut v___y_4056_: *mut LeanObject,
    mut v___y_4057_: *mut LeanObject,
    mut v___y_4058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4059_: *mut LeanObject = core::ptr::null_mut();
    v_res_4059_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(
        v_cls_4050_,
        v_msg_4051_,
        v___y_4052_,
        v___y_4053_,
        v___y_4054_,
        v___y_4055_,
        v___y_4056_,
        v___y_4057_,
    );
    lean_dec(v___y_4057_);
    lean_dec_ref(v___y_4056_);
    lean_dec(v___y_4055_);
    lean_dec_ref(v___y_4054_);
    lean_dec(v___y_4053_);
    lean_dec_ref(v___y_4052_);
    return v_res_4059_;
}
pub unsafe fn l_Lean_Meta_Sym_reportIssueIfVerbose(
    mut v_msg_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4068_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4061_);
                v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
                v_isSharedCheck_4079_ = (!lean_is_exclusive(v___x_4068_)) as u8;
                if v_isSharedCheck_4079_ == 0 {
                    v___x_4071_ = v___x_4068_;
                    v_isShared_4072_ = v_isSharedCheck_4079_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4069_);
                    lean_dec(v___x_4068_);
                    v___x_4071_ = lean_box(0);
                    v_isShared_4072_ = v_isSharedCheck_4079_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4073_ = (lean_unbox(v_a_4069_) as u8);
                lean_dec(v_a_4069_);
                if v___x_4073_ == 0 {
                    lean_dec_ref(v_msg_4060_);
                    v___x_4074_ = lean_box(0);
                    if v_isShared_4072_ == 0 {
                        lean_ctor_set(v___x_4071_, 0, v___x_4074_);
                        v___x_4076_ = v___x_4071_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4074_);
                        v___x_4076_ = v_reuseFailAlloc_4077_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4071_);
                    v___x_4078_ = l_Lean_Meta_Sym_reportIssue(
                        v_msg_4060_,
                        v_a_4061_,
                        v_a_4062_,
                        v_a_4063_,
                        v_a_4064_,
                        v_a_4065_,
                        v_a_4066_,
                    );
                    return v___x_4078_;
                }
            }
            2 => {
                return v___x_4076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_reportIssueIfVerbose___boxed(
    mut v_msg_4080_: *mut LeanObject,
    mut v_a_4081_: *mut LeanObject,
    mut v_a_4082_: *mut LeanObject,
    mut v_a_4083_: *mut LeanObject,
    mut v_a_4084_: *mut LeanObject,
    mut v_a_4085_: *mut LeanObject,
    mut v_a_4086_: *mut LeanObject,
    mut v_a_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4088_: *mut LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_Lean_Meta_Sym_reportIssueIfVerbose(
        v_msg_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
        v_a_4084_,
        v_a_4085_,
        v_a_4086_,
    );
    lean_dec(v_a_4086_);
    lean_dec_ref(v_a_4085_);
    lean_dec(v_a_4084_);
    lean_dec_ref(v_a_4083_);
    lean_dec(v_a_4082_);
    lean_dec_ref(v_a_4081_);
    return v_res_4088_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7()
-> *mut LeanObject {
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    v___x_4104_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6;
    v___x_4105_ = l_String_toRawSubstring_x27(v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24()
-> *mut LeanObject {
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_4143_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
    v___x_4144_ = l_String_toRawSubstring_x27(v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30()
-> *mut LeanObject {
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29;
    v___x_4157_ = l_String_toRawSubstring_x27(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
    mut v_s_4180_: *mut LeanObject,
    mut v_a_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: u8 = 0;
    let mut v_quotContext_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_s_4180_);
                v___x_4203_ = l_Lean_Syntax_getKind(v_s_4180_);
                v___x_4204_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16;
                v___x_4205_ = lean_name_eq(v___x_4203_, v___x_4204_);
                lean_dec(v___x_4203_);
                if v___x_4205_ == 0 {
                    v_quotContext_4206_ = lean_ctor_get(v_a_4181_, 1);
                    v_currMacroScope_4207_ = lean_ctor_get(v_a_4181_, 2);
                    v_ref_4208_ = lean_ctor_get(v_a_4181_, 5);
                    v___x_4209_ = l_Lean_SourceInfo_fromRef(v_ref_4208_, v___x_4205_);
                    v___x_4210_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18;
                    v___x_4211_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20;
                    v___x_4212_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21;
                    lean_inc_n(v___x_4209_, 8);
                    v___x_4213_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4213_, 0, v___x_4209_);
                    lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                    v___x_4214_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23;
                    v___x_4215_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
                    v___x_4216_ = lean_box(0);
                    lean_inc_n(v_currMacroScope_4207_, 3);
                    lean_inc_n(v_quotContext_4206_, 3);
                    v___x_4217_ = l_Lean_addMacroScope(
                        v_quotContext_4206_,
                        v___x_4216_,
                        v_currMacroScope_4207_,
                    );
                    v___x_4218_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27;
                    v___x_4219_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4219_, 0, v___x_4209_);
                    lean_ctor_set(v___x_4219_, 1, v___x_4215_);
                    lean_ctor_set(v___x_4219_, 2, v___x_4217_);
                    lean_ctor_set(v___x_4219_, 3, v___x_4218_);
                    v___x_4220_ = l_Lean_Syntax_node1(v___x_4209_, v___x_4214_, v___x_4219_);
                    v___x_4221_ =
                        l_Lean_Syntax_node2(v___x_4209_, v___x_4211_, v___x_4213_, v___x_4220_);
                    v___x_4222_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28;
                    v___x_4223_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4223_, 0, v___x_4209_);
                    lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                    v___x_4224_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                    v___x_4225_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
                    v___x_4226_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31;
                    v___x_4227_ = l_Lean_addMacroScope(
                        v_quotContext_4206_,
                        v___x_4226_,
                        v_currMacroScope_4207_,
                    );
                    v___x_4228_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36;
                    v___x_4229_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4229_, 0, v___x_4209_);
                    lean_ctor_set(v___x_4229_, 1, v___x_4225_);
                    lean_ctor_set(v___x_4229_, 2, v___x_4227_);
                    lean_ctor_set(v___x_4229_, 3, v___x_4228_);
                    v___x_4230_ = l_Lean_Syntax_node1(v___x_4209_, v___x_4224_, v___x_4229_);
                    v___x_4231_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37;
                    v___x_4232_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4232_, 0, v___x_4209_);
                    lean_ctor_set(v___x_4232_, 1, v___x_4231_);
                    v___x_4233_ = l_Lean_Syntax_node5(
                        v___x_4209_,
                        v___x_4210_,
                        v___x_4221_,
                        v_s_4180_,
                        v___x_4223_,
                        v___x_4230_,
                        v___x_4232_,
                    );
                    v_msg_4184_ = v___x_4233_;
                    v_quotContext_4185_ = v_quotContext_4206_;
                    v_currMacroScope_4186_ = v_currMacroScope_4207_;
                    v_ref_4187_ = v_ref_4208_;
                    v___y_4188_ = v_a_4182_;
                    state = 1;
                    continue;
                } else {
                    v_quotContext_4234_ = lean_ctor_get(v_a_4181_, 1);
                    v_currMacroScope_4235_ = lean_ctor_get(v_a_4181_, 2);
                    v_ref_4236_ = lean_ctor_get(v_a_4181_, 5);
                    v___x_4237_ = 0;
                    v___x_4238_ = l_Lean_SourceInfo_fromRef(v_ref_4236_, v___x_4237_);
                    v___x_4239_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39;
                    v___x_4240_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40;
                    lean_inc(v___x_4238_);
                    v___x_4241_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4241_, 0, v___x_4238_);
                    lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                    v___x_4242_ =
                        l_Lean_Syntax_node2(v___x_4238_, v___x_4239_, v___x_4241_, v_s_4180_);
                    lean_inc(v_currMacroScope_4235_);
                    lean_inc(v_quotContext_4234_);
                    v_msg_4184_ = v___x_4242_;
                    v_quotContext_4185_ = v_quotContext_4234_;
                    v_currMacroScope_4186_ = v_currMacroScope_4235_;
                    v_ref_4187_ = v_ref_4236_;
                    v___y_4188_ = v_a_4182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4189_ = 0;
                v___x_4190_ = l_Lean_SourceInfo_fromRef(v_ref_4187_, v___x_4189_);
                v___x_4191_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3;
                v___x_4192_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5;
                v___x_4193_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
                v___x_4194_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9;
                v___x_4195_ =
                    l_Lean_addMacroScope(v_quotContext_4185_, v___x_4194_, v_currMacroScope_4186_);
                v___x_4196_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12;
                lean_inc_n(v___x_4190_, 3);
                v___x_4197_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4197_, 0, v___x_4190_);
                lean_ctor_set(v___x_4197_, 1, v___x_4193_);
                lean_ctor_set(v___x_4197_, 2, v___x_4195_);
                lean_ctor_set(v___x_4197_, 3, v___x_4196_);
                v___x_4198_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                v___x_4199_ = l_Lean_Syntax_node1(v___x_4190_, v___x_4198_, v_msg_4184_);
                v___x_4200_ =
                    l_Lean_Syntax_node2(v___x_4190_, v___x_4192_, v___x_4197_, v___x_4199_);
                v___x_4201_ = l_Lean_Syntax_node1(v___x_4190_, v___x_4191_, v___x_4200_);
                v___x_4202_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4202_, 0, v___x_4201_);
                lean_ctor_set(v___x_4202_, 1, v___y_4188_);
                return v___x_4202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(
    mut v_s_4243_: *mut LeanObject,
    mut v_a_4244_: *mut LeanObject,
    mut v_a_4245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4246_: *mut LeanObject = core::ptr::null_mut();
    v_res_4246_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
        v_s_4243_, v_a_4244_, v_a_4245_,
    );
    lean_dec_ref(v_a_4244_);
    return v_res_4246_;
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(
    mut v_x_4287_: *mut LeanObject,
    mut v_a_4288_: *mut LeanObject,
    mut v_a_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4290_ = l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1;
                lean_inc(v_x_4287_);
                v___x_4291_ = l_Lean_Syntax_isOfKind(v_x_4287_, v___x_4290_);
                if v___x_4291_ == 0 {
                    lean_dec(v_x_4287_);
                    v___x_4292_ = lean_box(1);
                    v___x_4293_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4293_, 0, v___x_4292_);
                    lean_ctor_set(v___x_4293_, 1, v_a_4289_);
                    return v___x_4293_;
                } else {
                    v___x_4294_ = lean_unsigned_to_nat(1);
                    v___x_4295_ = l_Lean_Syntax_getArg(v_x_4287_, v___x_4294_);
                    lean_dec(v_x_4287_);
                    v___x_4296_ =
                        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
                            v___x_4295_,
                            v_a_4288_,
                            v_a_4289_,
                        );
                    v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
                    v_a_4298_ = lean_ctor_get(v___x_4296_, 1);
                    v_isSharedCheck_4305_ = (!lean_is_exclusive(v___x_4296_)) as u8;
                    if v_isSharedCheck_4305_ == 0 {
                        v___x_4300_ = v___x_4296_;
                        v_isShared_4301_ = v_isSharedCheck_4305_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4298_);
                        lean_inc(v_a_4297_);
                        lean_dec(v___x_4296_);
                        v___x_4300_ = lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4305_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4301_ == 0 {
                    v___x_4303_ = v___x_4300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4297_);
                    lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_a_4298_);
                    v___x_4303_ = v_reuseFailAlloc_4304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1___boxed(
    mut v_x_4306_: *mut LeanObject,
    mut v_a_4307_: *mut LeanObject,
    mut v_a_4308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4309_: *mut LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4306_, v_a_4307_, v_a_4308_);
    lean_dec_ref(v_a_4307_);
    return v_res_4309_;
}
pub unsafe fn l_Lean_Meta_Sym_reportDbgIssue(
    mut v_msg_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4318_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4311_);
                v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
                v_isSharedCheck_4338_ = (!lean_is_exclusive(v___x_4318_)) as u8;
                if v_isSharedCheck_4338_ == 0 {
                    v___x_4321_ = v___x_4318_;
                    v_isShared_4322_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4319_);
                    lean_dec(v___x_4318_);
                    v___x_4321_ = lean_box(0);
                    v_isShared_4322_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4323_ = (lean_unbox(v_a_4319_) as u8);
                lean_dec(v_a_4319_);
                if v___x_4323_ == 0 {
                    lean_dec_ref(v_msg_4310_);
                    v___x_4324_ = lean_box(0);
                    if v_isShared_4322_ == 0 {
                        lean_ctor_set(v___x_4321_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4321_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                        v___x_4326_ = v_reuseFailAlloc_4327_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_options_4328_ = lean_ctor_get(v_a_4315_, 2);
                    v___x_4329_ = l_Lean_KVMap_instValueBool;
                    v___x_4330_ = l_Lean_Meta_Sym_sym_debug;
                    v___x_4331_ =
                        l_Lean_Option_get___redArg(v___x_4329_, v_options_4328_, v___x_4330_);
                    v___x_4332_ = (lean_unbox(v___x_4331_) as u8);
                    lean_dec(v___x_4331_);
                    if v___x_4332_ == 0 {
                        lean_dec_ref(v_msg_4310_);
                        v___x_4333_ = lean_box(0);
                        if v_isShared_4322_ == 0 {
                            lean_ctor_set(v___x_4321_, 0, v___x_4333_);
                            v___x_4335_ = v___x_4321_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
                            v___x_4335_ = v_reuseFailAlloc_4336_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4321_);
                        v___x_4337_ = l_Lean_Meta_Sym_reportIssue(
                            v_msg_4310_,
                            v_a_4311_,
                            v_a_4312_,
                            v_a_4313_,
                            v_a_4314_,
                            v_a_4315_,
                            v_a_4316_,
                        );
                        return v___x_4337_;
                    }
                }
            }
            2 => {
                return v___x_4326_;
            }
            3 => {
                return v___x_4335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_reportDbgIssue___boxed(
    mut v_msg_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
    mut v_a_4343_: *mut LeanObject,
    mut v_a_4344_: *mut LeanObject,
    mut v_a_4345_: *mut LeanObject,
    mut v_a_4346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4347_: *mut LeanObject = core::ptr::null_mut();
    v_res_4347_ = l_Lean_Meta_Sym_reportDbgIssue(
        v_msg_4339_,
        v_a_4340_,
        v_a_4341_,
        v_a_4342_,
        v_a_4343_,
        v_a_4344_,
        v_a_4345_,
    );
    lean_dec(v_a_4345_);
    lean_dec_ref(v_a_4344_);
    lean_dec(v_a_4343_);
    lean_dec_ref(v_a_4342_);
    lean_dec(v_a_4341_);
    lean_dec_ref(v_a_4340_);
    return v_res_4347_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1() -> *mut LeanObject {
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    v___x_4349_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0;
    v___x_4350_ = l_String_toRawSubstring_x27(v___x_4349_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_Meta_Sym_expandReportDbgIssueMacro(
    mut v_s_4366_: *mut LeanObject,
    mut v_a_4367_: *mut LeanObject,
    mut v_a_4368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msg_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: u8 = 0;
    let mut v_quotContext_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_s_4366_);
                v___x_4389_ = l_Lean_Syntax_getKind(v_s_4366_);
                v___x_4390_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16;
                v___x_4391_ = lean_name_eq(v___x_4389_, v___x_4390_);
                lean_dec(v___x_4389_);
                if v___x_4391_ == 0 {
                    v_quotContext_4392_ = lean_ctor_get(v_a_4367_, 1);
                    v_currMacroScope_4393_ = lean_ctor_get(v_a_4367_, 2);
                    v_ref_4394_ = lean_ctor_get(v_a_4367_, 5);
                    v___x_4395_ = l_Lean_SourceInfo_fromRef(v_ref_4394_, v___x_4391_);
                    v___x_4396_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18;
                    v___x_4397_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20;
                    v___x_4398_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21;
                    lean_inc_n(v___x_4395_, 8);
                    v___x_4399_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4399_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                    v___x_4400_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23;
                    v___x_4401_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
                    v___x_4402_ = lean_box(0);
                    lean_inc_n(v_currMacroScope_4393_, 3);
                    lean_inc_n(v_quotContext_4392_, 3);
                    v___x_4403_ = l_Lean_addMacroScope(
                        v_quotContext_4392_,
                        v___x_4402_,
                        v_currMacroScope_4393_,
                    );
                    v___x_4404_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27;
                    v___x_4405_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4405_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4405_, 1, v___x_4401_);
                    lean_ctor_set(v___x_4405_, 2, v___x_4403_);
                    lean_ctor_set(v___x_4405_, 3, v___x_4404_);
                    v___x_4406_ = l_Lean_Syntax_node1(v___x_4395_, v___x_4400_, v___x_4405_);
                    v___x_4407_ =
                        l_Lean_Syntax_node2(v___x_4395_, v___x_4397_, v___x_4399_, v___x_4406_);
                    v___x_4408_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28;
                    v___x_4409_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4409_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4409_, 1, v___x_4408_);
                    v___x_4410_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                    v___x_4411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
                    v___x_4412_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31;
                    v___x_4413_ = l_Lean_addMacroScope(
                        v_quotContext_4392_,
                        v___x_4412_,
                        v_currMacroScope_4393_,
                    );
                    v___x_4414_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36;
                    v___x_4415_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_4415_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4415_, 1, v___x_4411_);
                    lean_ctor_set(v___x_4415_, 2, v___x_4413_);
                    lean_ctor_set(v___x_4415_, 3, v___x_4414_);
                    v___x_4416_ = l_Lean_Syntax_node1(v___x_4395_, v___x_4410_, v___x_4415_);
                    v___x_4417_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37;
                    v___x_4418_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4418_, 0, v___x_4395_);
                    lean_ctor_set(v___x_4418_, 1, v___x_4417_);
                    v___x_4419_ = l_Lean_Syntax_node5(
                        v___x_4395_,
                        v___x_4396_,
                        v___x_4407_,
                        v_s_4366_,
                        v___x_4409_,
                        v___x_4416_,
                        v___x_4418_,
                    );
                    v_msg_4370_ = v___x_4419_;
                    v_quotContext_4371_ = v_quotContext_4392_;
                    v_currMacroScope_4372_ = v_currMacroScope_4393_;
                    v_ref_4373_ = v_ref_4394_;
                    v___y_4374_ = v_a_4368_;
                    state = 1;
                    continue;
                } else {
                    v_quotContext_4420_ = lean_ctor_get(v_a_4367_, 1);
                    v_currMacroScope_4421_ = lean_ctor_get(v_a_4367_, 2);
                    v_ref_4422_ = lean_ctor_get(v_a_4367_, 5);
                    v___x_4423_ = 0;
                    v___x_4424_ = l_Lean_SourceInfo_fromRef(v_ref_4422_, v___x_4423_);
                    v___x_4425_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39;
                    v___x_4426_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40;
                    lean_inc(v___x_4424_);
                    v___x_4427_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_4427_, 0, v___x_4424_);
                    lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                    v___x_4428_ =
                        l_Lean_Syntax_node2(v___x_4424_, v___x_4425_, v___x_4427_, v_s_4366_);
                    lean_inc(v_currMacroScope_4421_);
                    lean_inc(v_quotContext_4420_);
                    v_msg_4370_ = v___x_4428_;
                    v_quotContext_4371_ = v_quotContext_4420_;
                    v_currMacroScope_4372_ = v_currMacroScope_4421_;
                    v_ref_4373_ = v_ref_4422_;
                    v___y_4374_ = v_a_4368_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4375_ = 0;
                v___x_4376_ = l_Lean_SourceInfo_fromRef(v_ref_4373_, v___x_4375_);
                v___x_4377_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3;
                v___x_4378_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5;
                v___x_4379_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once
                    ),
                    _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1,
                );
                v___x_4380_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3;
                v___x_4381_ =
                    l_Lean_addMacroScope(v_quotContext_4371_, v___x_4380_, v_currMacroScope_4372_);
                v___x_4382_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6;
                lean_inc_n(v___x_4376_, 3);
                v___x_4383_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_4383_, 0, v___x_4376_);
                lean_ctor_set(v___x_4383_, 1, v___x_4379_);
                lean_ctor_set(v___x_4383_, 2, v___x_4381_);
                lean_ctor_set(v___x_4383_, 3, v___x_4382_);
                v___x_4384_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                v___x_4385_ = l_Lean_Syntax_node1(v___x_4376_, v___x_4384_, v_msg_4370_);
                v___x_4386_ =
                    l_Lean_Syntax_node2(v___x_4376_, v___x_4378_, v___x_4383_, v___x_4385_);
                v___x_4387_ = l_Lean_Syntax_node1(v___x_4376_, v___x_4377_, v___x_4386_);
                v___x_4388_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4388_, 0, v___x_4387_);
                lean_ctor_set(v___x_4388_, 1, v___y_4374_);
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(
    mut v_s_4429_: *mut LeanObject,
    mut v_a_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4432_: *mut LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4429_, v_a_4430_, v_a_4431_);
    lean_dec_ref(v_a_4430_);
    return v_res_4432_;
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(
    mut v_x_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4454_ = l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1;
                lean_inc(v_x_4451_);
                v___x_4455_ = l_Lean_Syntax_isOfKind(v_x_4451_, v___x_4454_);
                if v___x_4455_ == 0 {
                    lean_dec(v_x_4451_);
                    v___x_4456_ = lean_box(1);
                    v___x_4457_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4457_, 0, v___x_4456_);
                    lean_ctor_set(v___x_4457_, 1, v_a_4453_);
                    return v___x_4457_;
                } else {
                    v___x_4458_ = lean_unsigned_to_nat(1);
                    v___x_4459_ = l_Lean_Syntax_getArg(v_x_4451_, v___x_4458_);
                    lean_dec(v_x_4451_);
                    v___x_4460_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(
                        v___x_4459_,
                        v_a_4452_,
                        v_a_4453_,
                    );
                    v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
                    v_a_4462_ = lean_ctor_get(v___x_4460_, 1);
                    v_isSharedCheck_4469_ = (!lean_is_exclusive(v___x_4460_)) as u8;
                    if v_isSharedCheck_4469_ == 0 {
                        v___x_4464_ = v___x_4460_;
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4462_);
                        lean_inc(v_a_4461_);
                        lean_dec(v___x_4460_);
                        v___x_4464_ = lean_box(0);
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4465_ == 0 {
                    v___x_4467_ = v___x_4464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4461_);
                    lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_a_4462_);
                    v___x_4467_ = v_reuseFailAlloc_4468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1___boxed(
    mut v_x_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4473_: *mut LeanObject = core::ptr::null_mut();
    v_res_4473_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4470_, v_a_4471_, v_a_4472_);
    lean_dec_ref(v_a_4471_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___redArg(
    mut v_a_4474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    v___x_4476_ = lean_st_ref_get(v_a_4474_);
    v_issues_4477_ = lean_ctor_get(v___x_4476_, 8);
    lean_inc(v_issues_4477_);
    lean_dec(v___x_4476_);
    v___x_4478_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4478_, 0, v_issues_4477_);
    return v___x_4478_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___redArg___boxed(
    mut v_a_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4481_: *mut LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4479_);
    lean_dec(v_a_4479_);
    return v_res_4481_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues(
    mut v_a_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
    mut v_a_4487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4489_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4483_);
    return v___x_4489_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___boxed(
    mut v_a_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
    mut v_a_4492_: *mut LeanObject,
    mut v_a_4493_: *mut LeanObject,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4497_: *mut LeanObject = core::ptr::null_mut();
    v_res_4497_ = l_Lean_Meta_Sym_getIssues(
        v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_,
    );
    lean_dec(v_a_4495_);
    lean_dec_ref(v_a_4494_);
    lean_dec(v_a_4493_);
    lean_dec_ref(v_a_4492_);
    lean_dec(v_a_4491_);
    lean_dec_ref(v_a_4490_);
    return v_res_4497_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
    mut v_a_4498_: *mut LeanObject,
    mut v_issues_4499_: *mut LeanObject,
    mut v_a_x3f_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4513_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4502_ = lean_st_ref_take(v_a_4498_);
                v_share_4503_ = lean_ctor_get(v___x_4502_, 0);
                v_maxFVar_4504_ = lean_ctor_get(v___x_4502_, 1);
                v_proofInstInfo_4505_ = lean_ctor_get(v___x_4502_, 2);
                v_inferType_4506_ = lean_ctor_get(v___x_4502_, 3);
                v_getLevel_4507_ = lean_ctor_get(v___x_4502_, 4);
                v_congrInfo_4508_ = lean_ctor_get(v___x_4502_, 5);
                v_defEqI_4509_ = lean_ctor_get(v___x_4502_, 6);
                v_extensions_4510_ = lean_ctor_get(v___x_4502_, 7);
                v_issues_4511_ = lean_ctor_get(v___x_4502_, 8);
                v_canon_4512_ = lean_ctor_get(v___x_4502_, 9);
                v_debug_4513_ = lean_ctor_get_uint8(
                    v___x_4502_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4524_ = (!lean_is_exclusive(v___x_4502_)) as u8;
                if v_isSharedCheck_4524_ == 0 {
                    v___x_4515_ = v___x_4502_;
                    v_isShared_4516_ = v_isSharedCheck_4524_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_4512_);
                    lean_inc(v_issues_4511_);
                    lean_inc(v_extensions_4510_);
                    lean_inc(v_defEqI_4509_);
                    lean_inc(v_congrInfo_4508_);
                    lean_inc(v_getLevel_4507_);
                    lean_inc(v_inferType_4506_);
                    lean_inc(v_proofInstInfo_4505_);
                    lean_inc(v_maxFVar_4504_);
                    lean_inc(v_share_4503_);
                    lean_dec(v___x_4502_);
                    v___x_4515_ = lean_box(0);
                    v_isShared_4516_ = v_isSharedCheck_4524_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4517_ = l_List_appendTR___redArg(v_issues_4511_, v_issues_4499_);
                if v_isShared_4516_ == 0 {
                    lean_ctor_set(v___x_4515_, 8, v___x_4517_);
                    v___x_4519_ = v___x_4515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_share_4503_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_maxFVar_4504_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 2, v_proofInstInfo_4505_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 3, v_inferType_4506_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 4, v_getLevel_4507_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 5, v_congrInfo_4508_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 6, v_defEqI_4509_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 7, v_extensions_4510_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 8, v___x_4517_);
                    lean_ctor_set(v_reuseFailAlloc_4523_, 9, v_canon_4512_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4523_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4513_,
                    );
                    v___x_4519_ = v_reuseFailAlloc_4523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4520_ = lean_st_ref_set(v_a_4498_, v___x_4519_);
                v___x_4521_ = lean_box(0);
                v___x_4522_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4522_, 0, v___x_4521_);
                return v___x_4522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(
    mut v_a_4525_: *mut LeanObject,
    mut v_issues_4526_: *mut LeanObject,
    mut v_a_x3f_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4529_: *mut LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
        v_a_4525_,
        v_issues_4526_,
        v_a_x3f_4527_,
    );
    lean_dec(v_a_x3f_4527_);
    lean_dec(v_a_4525_);
    return v_res_4529_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg(
    mut v_x_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
    mut v_a_4535_: *mut LeanObject,
    mut v_a_4536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4549_: u8 = 0;
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_unused_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_a_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_unused_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v_unused_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4538_ = lean_st_ref_get(v_a_4532_);
                v___x_4539_ = lean_st_ref_take(v_a_4532_);
                v_share_4540_ = lean_ctor_get(v___x_4539_, 0);
                v_maxFVar_4541_ = lean_ctor_get(v___x_4539_, 1);
                v_proofInstInfo_4542_ = lean_ctor_get(v___x_4539_, 2);
                v_inferType_4543_ = lean_ctor_get(v___x_4539_, 3);
                v_getLevel_4544_ = lean_ctor_get(v___x_4539_, 4);
                v_congrInfo_4545_ = lean_ctor_get(v___x_4539_, 5);
                v_defEqI_4546_ = lean_ctor_get(v___x_4539_, 6);
                v_extensions_4547_ = lean_ctor_get(v___x_4539_, 7);
                v_canon_4548_ = lean_ctor_get(v___x_4539_, 9);
                v_debug_4549_ = lean_ctor_get_uint8(
                    v___x_4539_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4588_ = (!lean_is_exclusive(v___x_4539_)) as u8;
                if v_isSharedCheck_4588_ == 0 {
                    v_unused_4589_ = lean_ctor_get(v___x_4539_, 8);
                    lean_dec(v_unused_4589_);
                    v___x_4551_ = v___x_4539_;
                    v_isShared_4552_ = v_isSharedCheck_4588_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_4548_);
                    lean_inc(v_extensions_4547_);
                    lean_inc(v_defEqI_4546_);
                    lean_inc(v_congrInfo_4545_);
                    lean_inc(v_getLevel_4544_);
                    lean_inc(v_inferType_4543_);
                    lean_inc(v_proofInstInfo_4542_);
                    lean_inc(v_maxFVar_4541_);
                    lean_inc(v_share_4540_);
                    lean_dec(v___x_4539_);
                    v___x_4551_ = lean_box(0);
                    v_isShared_4552_ = v_isSharedCheck_4588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4553_ = lean_box(0);
                if v_isShared_4552_ == 0 {
                    lean_ctor_set(v___x_4551_, 8, v___x_4553_);
                    v___x_4555_ = v___x_4551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_share_4540_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_maxFVar_4541_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_proofInstInfo_4542_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 3, v_inferType_4543_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_getLevel_4544_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 5, v_congrInfo_4545_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 6, v_defEqI_4546_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 7, v_extensions_4547_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 8, v___x_4553_);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 9, v_canon_4548_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4587_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4549_,
                    );
                    v___x_4555_ = v_reuseFailAlloc_4587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4556_ = lean_st_ref_set(v_a_4532_, v___x_4555_);
                v_issues_4557_ = lean_ctor_get(v___x_4538_, 8);
                lean_inc(v_issues_4557_);
                lean_dec(v___x_4538_);
                lean_inc(v_a_4536_);
                lean_inc_ref(v_a_4535_);
                lean_inc(v_a_4534_);
                lean_inc_ref(v_a_4533_);
                lean_inc(v_a_4532_);
                lean_inc_ref(v_a_4531_);
                v_r_4558_ = lean_apply_7(
                    v_x_4530_,
                    v_a_4531_,
                    v_a_4532_,
                    v_a_4533_,
                    v_a_4534_,
                    v_a_4535_,
                    v_a_4536_,
                    lean_box(0),
                );
                if lean_obj_tag(v_r_4558_) == 0 {
                    v_a_4559_ = lean_ctor_get(v_r_4558_, 0);
                    v_isSharedCheck_4575_ = (!lean_is_exclusive(v_r_4558_)) as u8;
                    if v_isSharedCheck_4575_ == 0 {
                        v___x_4561_ = v_r_4558_;
                        v_isShared_4562_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4559_);
                        lean_dec(v_r_4558_);
                        v___x_4561_ = lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4576_ = lean_ctor_get(v_r_4558_, 0);
                    lean_inc(v_a_4576_);
                    lean_dec_ref_known(v_r_4558_, 1);
                    v___x_4577_ = lean_box(0);
                    v___x_4578_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
                        v_a_4532_,
                        v_issues_4557_,
                        v___x_4577_,
                    );
                    v_isSharedCheck_4585_ = (!lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4585_ == 0 {
                        v_unused_4586_ = lean_ctor_get(v___x_4578_, 0);
                        lean_dec(v_unused_4586_);
                        v___x_4580_ = v___x_4578_;
                        v_isShared_4581_ = v_isSharedCheck_4585_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_4578_);
                        v___x_4580_ = lean_box(0);
                        v_isShared_4581_ = v_isSharedCheck_4585_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_4559_);
                if v_isShared_4562_ == 0 {
                    lean_ctor_set_tag(v___x_4561_, 1);
                    v___x_4564_ = v___x_4561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4559_);
                    v___x_4564_ = v_reuseFailAlloc_4574_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4565_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
                    v_a_4532_,
                    v_issues_4557_,
                    v___x_4564_,
                );
                lean_dec_ref(v___x_4564_);
                v_isSharedCheck_4572_ = (!lean_is_exclusive(v___x_4565_)) as u8;
                if v_isSharedCheck_4572_ == 0 {
                    v_unused_4573_ = lean_ctor_get(v___x_4565_, 0);
                    lean_dec(v_unused_4573_);
                    v___x_4567_ = v___x_4565_;
                    v_isShared_4568_ = v_isSharedCheck_4572_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_4565_);
                    v___x_4567_ = lean_box(0);
                    v_isShared_4568_ = v_isSharedCheck_4572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4568_ == 0 {
                    lean_ctor_set(v___x_4567_, 0, v_a_4559_);
                    v___x_4570_ = v___x_4567_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4559_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4570_;
            }
            7 => {
                if v_isShared_4581_ == 0 {
                    lean_ctor_set_tag(v___x_4580_, 1);
                    lean_ctor_set(v___x_4580_, 0, v_a_4576_);
                    v___x_4583_ = v___x_4580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4576_);
                    v___x_4583_ = v_reuseFailAlloc_4584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg___boxed(
    mut v_x_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
    mut v_a_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
    mut v_a_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4598_: *mut LeanObject = core::ptr::null_mut();
    v_res_4598_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(
        v_x_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_,
    );
    lean_dec(v_a_4596_);
    lean_dec_ref(v_a_4595_);
    lean_dec(v_a_4594_);
    lean_dec_ref(v_a_4593_);
    lean_dec(v_a_4592_);
    lean_dec_ref(v_a_4591_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext(
    mut v_00_u03b1_4599_: *mut LeanObject,
    mut v_x_4600_: *mut LeanObject,
    mut v_a_4601_: *mut LeanObject,
    mut v_a_4602_: *mut LeanObject,
    mut v_a_4603_: *mut LeanObject,
    mut v_a_4604_: *mut LeanObject,
    mut v_a_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    v___x_4608_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(
        v_x_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_,
    );
    return v___x_4608_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___boxed(
    mut v_00_u03b1_4609_: *mut LeanObject,
    mut v_x_4610_: *mut LeanObject,
    mut v_a_4611_: *mut LeanObject,
    mut v_a_4612_: *mut LeanObject,
    mut v_a_4613_: *mut LeanObject,
    mut v_a_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v_a_4616_: *mut LeanObject,
    mut v_a_4617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4618_: *mut LeanObject = core::ptr::null_mut();
    v_res_4618_ = l_Lean_Meta_Sym_withNewIssueContext(
        v_00_u03b1_4609_,
        v_x_4610_,
        v_a_4611_,
        v_a_4612_,
        v_a_4613_,
        v_a_4614_,
        v_a_4615_,
        v_a_4616_,
    );
    lean_dec(v_a_4616_);
    lean_dec_ref(v_a_4615_);
    lean_dec(v_a_4614_);
    lean_dec_ref(v_a_4613_);
    lean_dec(v_a_4612_);
    lean_dec_ref(v_a_4611_);
    return v_res_4618_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4619_: *mut LeanObject,
    mut v_vals_4620_: *mut LeanObject,
    mut v_i_4621_: *mut LeanObject,
    mut v_k_4622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4624_: u8 = 0;
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: u8 = 0;
    let mut v___x_4639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4630_ = lean_array_get_size(v_keys_4619_);
                v___x_4631_ = lean_nat_dec_lt(v_i_4621_, v___x_4630_);
                if v___x_4631_ == 0 {
                    lean_dec(v_i_4621_);
                    v___x_4632_ = lean_box(0);
                    return v___x_4632_;
                } else {
                    v_fst_4633_ = lean_ctor_get(v_k_4622_, 0);
                    v_snd_4634_ = lean_ctor_get(v_k_4622_, 1);
                    v_k_x27_4635_ = lean_array_fget_borrowed(v_keys_4619_, v_i_4621_);
                    v_fst_4636_ = lean_ctor_get(v_k_x27_4635_, 0);
                    v_snd_4637_ = lean_ctor_get(v_k_x27_4635_, 1);
                    v___x_4638_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_4633_,
                            v_fst_4636_,
                        );
                    if v___x_4638_ == 0 {
                        v___y_4624_ = v___x_4638_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4639_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_snd_4634_,
                                v_snd_4637_,
                            );
                        v___y_4624_ = v___x_4639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4624_ == 0 {
                    v___x_4625_ = lean_unsigned_to_nat(1);
                    v___x_4626_ = lean_nat_add(v_i_4621_, v___x_4625_);
                    lean_dec(v_i_4621_);
                    v_i_4621_ = v___x_4626_;
                    state = 0;
                    continue;
                } else {
                    v___x_4628_ = lean_array_fget_borrowed(v_vals_4620_, v_i_4621_);
                    lean_dec(v_i_4621_);
                    lean_inc(v___x_4628_);
                    v___x_4629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4629_, 0, v___x_4628_);
                    return v___x_4629_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4640_: *mut LeanObject,
    mut v_vals_4641_: *mut LeanObject,
    mut v_i_4642_: *mut LeanObject,
    mut v_k_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4644_: *mut LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4640_, v_vals_4641_, v_i_4642_, v_k_4643_);
    lean_dec_ref(v_k_4643_);
    lean_dec_ref(v_vals_4641_);
    lean_dec_ref(v_keys_4640_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(
    mut v_x_4645_: *mut LeanObject,
    mut v_x_4646_: usize,
    mut v_x_4647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: usize = 0;
    let mut v___x_4651_: usize = 0;
    let mut v___x_4652_: usize = 0;
    let mut v_j_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4658_: u8 = 0;
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: u8 = 0;
    let mut v___x_4666_: u8 = 0;
    let mut v_node_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: usize = 0;
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4645_) == 0 {
                    v_es_4648_ = lean_ctor_get(v_x_4645_, 0);
                    v___x_4649_ = lean_box(2);
                    v___x_4650_ = 5usize;
                    v___x_4651_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_4652_ = lean_usize_land(v_x_4646_, v___x_4651_);
                    v_j_4653_ = lean_usize_to_nat(v___x_4652_);
                    v___x_4654_ = lean_array_get_borrowed(v___x_4649_, v_es_4648_, v_j_4653_);
                    lean_dec(v_j_4653_);
                    match lean_obj_tag(v___x_4654_) {
                        0 => {
                            v_key_4655_ = lean_ctor_get(v___x_4654_, 0);
                            v_val_4656_ = lean_ctor_get(v___x_4654_, 1);
                            v_fst_4661_ = lean_ctor_get(v_x_4647_, 0);
                            v_snd_4662_ = lean_ctor_get(v_x_4647_, 1);
                            v_fst_4663_ = lean_ctor_get(v_key_4655_, 0);
                            v_snd_4664_ = lean_ctor_get(v_key_4655_, 1);
                            v___x_4665_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_4661_, v_fst_4663_);
                            if v___x_4665_ == 0 {
                                v___y_4658_ = v___x_4665_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4666_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_snd_4662_, v_snd_4664_);
                                v___y_4658_ = v___x_4666_;
                                state = 1;
                                continue;
                            }
                        }
                        1 => {
                            v_node_4667_ = lean_ctor_get(v___x_4654_, 0);
                            v___x_4668_ = lean_usize_shift_right(v_x_4646_, v___x_4650_);
                            v_x_4645_ = v_node_4667_;
                            v_x_4646_ = v___x_4668_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4670_ = lean_box(0);
                            return v___x_4670_;
                        }
                    }
                } else {
                    v_ks_4671_ = lean_ctor_get(v_x_4645_, 0);
                    v_vs_4672_ = lean_ctor_get(v_x_4645_, 1);
                    v___x_4673_ = lean_unsigned_to_nat(0);
                    v___x_4674_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4671_, v_vs_4672_, v___x_4673_, v_x_4647_);
                    return v___x_4674_;
                }
            }
            1 => {
                if v___y_4658_ == 0 {
                    v___x_4659_ = lean_box(0);
                    return v___x_4659_;
                } else {
                    lean_inc(v_val_4656_);
                    v___x_4660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4660_, 0, v_val_4656_);
                    return v___x_4660_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(
    mut v_x_4675_: *mut LeanObject,
    mut v_x_4676_: *mut LeanObject,
    mut v_x_4677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2658__boxed_4678_: usize = 0;
    let mut v_res_4679_: *mut LeanObject = core::ptr::null_mut();
    v_x_2658__boxed_4678_ = lean_unbox_usize(v_x_4676_);
    lean_dec(v_x_4676_);
    v_res_4679_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4675_, v_x_2658__boxed_4678_, v_x_4677_);
    lean_dec_ref(v_x_4677_);
    lean_dec_ref(v_x_4675_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
    mut v_x_4680_: *mut LeanObject,
    mut v_x_4681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u64 = 0;
    let mut v___x_4685_: u64 = 0;
    let mut v___x_4686_: u64 = 0;
    let mut v___x_4687_: usize = 0;
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4682_ = lean_ctor_get(v_x_4681_, 0);
    v_snd_4683_ = lean_ctor_get(v_x_4681_, 1);
    v___x_4684_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4682_);
    v___x_4685_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4683_);
    v___x_4686_ = lean_uint64_mix_hash(v___x_4684_, v___x_4685_);
    v___x_4687_ = lean_uint64_to_usize(v___x_4686_);
    v___x_4688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4680_, v___x_4687_, v_x_4681_);
    return v___x_4688_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(
    mut v_x_4689_: *mut LeanObject,
    mut v_x_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
            v_x_4689_, v_x_4690_,
        );
    lean_dec_ref(v_x_4690_);
    lean_dec_ref(v_x_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_4692_: *mut LeanObject,
    mut v_x_4693_: *mut LeanObject,
    mut v_x_4694_: *mut LeanObject,
    mut v_x_4695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v___y_4702_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: u8 = 0;
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4696_ = lean_ctor_get(v_x_4692_, 0);
                v_vs_4697_ = lean_ctor_get(v_x_4692_, 1);
                v_isSharedCheck_4726_ = (!lean_is_exclusive(v_x_4692_)) as u8;
                if v_isSharedCheck_4726_ == 0 {
                    v___x_4699_ = v_x_4692_;
                    v_isShared_4700_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4697_);
                    lean_inc(v_ks_4696_);
                    lean_dec(v_x_4692_);
                    v___x_4699_ = lean_box(0);
                    v_isShared_4700_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4714_ = lean_array_get_size(v_ks_4696_);
                v___x_4715_ = lean_nat_dec_lt(v_x_4693_, v___x_4714_);
                if v___x_4715_ == 0 {
                    lean_del_object(v___x_4699_);
                    lean_dec(v_x_4693_);
                    v___x_4716_ = lean_array_push(v_ks_4696_, v_x_4694_);
                    v___x_4717_ = lean_array_push(v_vs_4697_, v_x_4695_);
                    v___x_4718_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4718_, 0, v___x_4716_);
                    lean_ctor_set(v___x_4718_, 1, v___x_4717_);
                    return v___x_4718_;
                } else {
                    v_fst_4719_ = lean_ctor_get(v_x_4694_, 0);
                    v_snd_4720_ = lean_ctor_get(v_x_4694_, 1);
                    v_k_x27_4721_ = lean_array_fget_borrowed(v_ks_4696_, v_x_4693_);
                    v_fst_4722_ = lean_ctor_get(v_k_x27_4721_, 0);
                    v_snd_4723_ = lean_ctor_get(v_k_x27_4721_, 1);
                    v___x_4724_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_4719_,
                            v_fst_4722_,
                        );
                    if v___x_4724_ == 0 {
                        v___y_4702_ = v___x_4724_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4725_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_snd_4720_,
                                v_snd_4723_,
                            );
                        v___y_4702_ = v___x_4725_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_4702_ == 0 {
                    if v_isShared_4700_ == 0 {
                        v___x_4704_ = v___x_4699_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_ks_4696_);
                        lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_vs_4697_);
                        v___x_4704_ = v_reuseFailAlloc_4708_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4709_ = lean_array_fset(v_ks_4696_, v_x_4693_, v_x_4694_);
                    v___x_4710_ = lean_array_fset(v_vs_4697_, v_x_4693_, v_x_4695_);
                    lean_dec(v_x_4693_);
                    if v_isShared_4700_ == 0 {
                        lean_ctor_set(v___x_4699_, 1, v___x_4710_);
                        lean_ctor_set(v___x_4699_, 0, v___x_4709_);
                        v___x_4712_ = v___x_4699_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4709_);
                        lean_ctor_set(v_reuseFailAlloc_4713_, 1, v___x_4710_);
                        v___x_4712_ = v_reuseFailAlloc_4713_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4705_ = lean_unsigned_to_nat(1);
                v___x_4706_ = lean_nat_add(v_x_4693_, v___x_4705_);
                lean_dec(v_x_4693_);
                v_x_4692_ = v___x_4704_;
                v_x_4693_ = v___x_4706_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(
    mut v_n_4727_: *mut LeanObject,
    mut v_k_4728_: *mut LeanObject,
    mut v_v_4729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    v___x_4730_ = lean_unsigned_to_nat(0);
    v___x_4731_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4727_, v___x_4730_, v_k_4728_, v_v_4729_);
    return v___x_4731_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4732_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(
    mut v_x_4733_: *mut LeanObject,
    mut v_x_4734_: usize,
    mut v_x_4735_: usize,
    mut v_x_4736_: *mut LeanObject,
    mut v_x_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: usize = 0;
    let mut v___x_4740_: usize = 0;
    let mut v___x_4741_: usize = 0;
    let mut v___x_4742_: usize = 0;
    let mut v_j_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: u8 = 0;
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v_v_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___y_4764_: u8 = 0;
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: u8 = 0;
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut v_node_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4781_: usize = 0;
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut v_unused_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: u8 = 0;
    let mut v_ks_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: usize = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v_reuseFailAlloc_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4733_) == 0 {
                    v_es_4738_ = lean_ctor_get(v_x_4733_, 0);
                    v___x_4739_ = 5usize;
                    v___x_4740_ = 1usize;
                    v___x_4741_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_4742_ = lean_usize_land(v_x_4734_, v___x_4741_);
                    v_j_4743_ = lean_usize_to_nat(v___x_4742_);
                    v___x_4744_ = lean_array_get_size(v_es_4738_);
                    v___x_4745_ = lean_nat_dec_lt(v_j_4743_, v___x_4744_);
                    if v___x_4745_ == 0 {
                        lean_dec(v_j_4743_);
                        lean_dec(v_x_4737_);
                        lean_dec_ref(v_x_4736_);
                        return v_x_4733_;
                    } else {
                        lean_inc_ref(v_es_4738_);
                        v_isSharedCheck_4789_ = (!lean_is_exclusive(v_x_4733_)) as u8;
                        if v_isSharedCheck_4789_ == 0 {
                            v_unused_4790_ = lean_ctor_get(v_x_4733_, 0);
                            lean_dec(v_unused_4790_);
                            v___x_4747_ = v_x_4733_;
                            v_isShared_4748_ = v_isSharedCheck_4789_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4733_);
                            v___x_4747_ = lean_box(0);
                            v_isShared_4748_ = v_isSharedCheck_4789_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4791_ = lean_ctor_get(v_x_4733_, 0);
                    v_vs_4792_ = lean_ctor_get(v_x_4733_, 1);
                    v_isSharedCheck_4812_ = (!lean_is_exclusive(v_x_4733_)) as u8;
                    if v_isSharedCheck_4812_ == 0 {
                        v___x_4794_ = v_x_4733_;
                        v_isShared_4795_ = v_isSharedCheck_4812_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_vs_4792_);
                        lean_inc(v_ks_4791_);
                        lean_dec(v_x_4733_);
                        v___x_4794_ = lean_box(0);
                        v_isShared_4795_ = v_isSharedCheck_4812_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4749_ = lean_array_fget(v_es_4738_, v_j_4743_);
                v___x_4750_ = lean_box(0);
                v_xs_x27_4751_ = lean_array_fset(v_es_4738_, v_j_4743_, v___x_4750_);
                match lean_obj_tag(v_v_4749_) {
                    0 => {
                        v_key_4758_ = lean_ctor_get(v_v_4749_, 0);
                        v_val_4759_ = lean_ctor_get(v_v_4749_, 1);
                        v_isSharedCheck_4776_ = (!lean_is_exclusive(v_v_4749_)) as u8;
                        if v_isSharedCheck_4776_ == 0 {
                            v___x_4761_ = v_v_4749_;
                            v_isShared_4762_ = v_isSharedCheck_4776_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4759_);
                            lean_inc(v_key_4758_);
                            lean_dec(v_v_4749_);
                            v___x_4761_ = lean_box(0);
                            v_isShared_4762_ = v_isSharedCheck_4776_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4777_ = lean_ctor_get(v_v_4749_, 0);
                        v_isSharedCheck_4787_ = (!lean_is_exclusive(v_v_4749_)) as u8;
                        if v_isSharedCheck_4787_ == 0 {
                            v___x_4779_ = v_v_4749_;
                            v_isShared_4780_ = v_isSharedCheck_4787_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_node_4777_);
                            lean_dec(v_v_4749_);
                            v___x_4779_ = lean_box(0);
                            v_isShared_4780_ = v_isSharedCheck_4787_;
                            state = 7;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4788_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4788_, 0, v_x_4736_);
                        lean_ctor_set(v___x_4788_, 1, v_x_4737_);
                        v___y_4753_ = v___x_4788_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4754_ = lean_array_fset(v_xs_x27_4751_, v_j_4743_, v___y_4753_);
                lean_dec(v_j_4743_);
                if v_isShared_4748_ == 0 {
                    lean_ctor_set(v___x_4747_, 0, v___x_4754_);
                    v___x_4756_ = v___x_4747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
                    v___x_4756_ = v_reuseFailAlloc_4757_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4756_;
            }
            4 => {
                v_fst_4770_ = lean_ctor_get(v_x_4736_, 0);
                v_snd_4771_ = lean_ctor_get(v_x_4736_, 1);
                v_fst_4772_ = lean_ctor_get(v_key_4758_, 0);
                v_snd_4773_ = lean_ctor_get(v_key_4758_, 1);
                v___x_4774_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fst_4770_,
                        v_fst_4772_,
                    );
                if v___x_4774_ == 0 {
                    v___y_4764_ = v___x_4774_;
                    state = 5;
                    continue;
                } else {
                    v___x_4775_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_snd_4771_,
                            v_snd_4773_,
                        );
                    v___y_4764_ = v___x_4775_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_4764_ == 0 {
                    lean_del_object(v___x_4761_);
                    v___x_4765_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4758_,
                        v_val_4759_,
                        v_x_4736_,
                        v_x_4737_,
                    );
                    v___x_4766_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4766_, 0, v___x_4765_);
                    v___y_4753_ = v___x_4766_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4759_);
                    lean_dec(v_key_4758_);
                    if v_isShared_4762_ == 0 {
                        lean_ctor_set(v___x_4761_, 1, v_x_4737_);
                        lean_ctor_set(v___x_4761_, 0, v_x_4736_);
                        v___x_4768_ = v___x_4761_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4769_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_x_4736_);
                        lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_x_4737_);
                        v___x_4768_ = v_reuseFailAlloc_4769_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___y_4753_ = v___x_4768_;
                state = 2;
                continue;
            }
            7 => {
                v___x_4781_ = lean_usize_shift_right(v_x_4734_, v___x_4739_);
                v___x_4782_ = lean_usize_add(v_x_4735_, v___x_4740_);
                v___x_4783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_node_4777_, v___x_4781_, v___x_4782_, v_x_4736_, v_x_4737_);
                if v_isShared_4780_ == 0 {
                    lean_ctor_set(v___x_4779_, 0, v___x_4783_);
                    v___x_4785_ = v___x_4779_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_4753_ = v___x_4785_;
                state = 2;
                continue;
            }
            9 => {
                if v_isShared_4795_ == 0 {
                    v___x_4797_ = v___x_4794_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_ks_4791_);
                    lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_vs_4792_);
                    v___x_4797_ = v_reuseFailAlloc_4811_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_newNode_4798_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v___x_4797_, v_x_4736_, v_x_4737_);
                v___x_4806_ = 7usize;
                v___x_4807_ = lean_usize_dec_le(v___x_4806_, v_x_4735_);
                if v___x_4807_ == 0 {
                    v___x_4808_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4798_);
                    v___x_4809_ = lean_unsigned_to_nat(4);
                    v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
                    lean_dec(v___x_4808_);
                    v___y_4800_ = v___x_4810_;
                    state = 11;
                    continue;
                } else {
                    v___y_4800_ = v___x_4807_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v___y_4800_ == 0 {
                    v_ks_4801_ = lean_ctor_get(v_newNode_4798_, 0);
                    lean_inc_ref(v_ks_4801_);
                    v_vs_4802_ = lean_ctor_get(v_newNode_4798_, 1);
                    lean_inc_ref(v_vs_4802_);
                    lean_dec_ref(v_newNode_4798_);
                    v___x_4803_ = lean_unsigned_to_nat(0);
                    v___x_4804_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
                    v___x_4805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4735_, v_ks_4801_, v_vs_4802_, v___x_4803_, v___x_4804_);
                    lean_dec_ref(v_vs_4802_);
                    lean_dec_ref(v_ks_4801_);
                    return v___x_4805_;
                } else {
                    return v_newNode_4798_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(
    mut v_depth_4813_: usize,
    mut v_keys_4814_: *mut LeanObject,
    mut v_vals_4815_: *mut LeanObject,
    mut v_i_4816_: *mut LeanObject,
    mut v_entries_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: u8 = 0;
    let mut v_k_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u64 = 0;
    let mut v___x_4825_: u64 = 0;
    let mut v___x_4826_: u64 = 0;
    let mut v_h_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: usize = 0;
    let mut v___x_4831_: usize = 0;
    let mut v___x_4832_: usize = 0;
    let mut v_h_4833_: usize = 0;
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4818_ = lean_array_get_size(v_keys_4814_);
                v___x_4819_ = lean_nat_dec_lt(v_i_4816_, v___x_4818_);
                if v___x_4819_ == 0 {
                    lean_dec(v_i_4816_);
                    return v_entries_4817_;
                } else {
                    v_k_4820_ = lean_array_fget_borrowed(v_keys_4814_, v_i_4816_);
                    v_fst_4821_ = lean_ctor_get(v_k_4820_, 0);
                    v_snd_4822_ = lean_ctor_get(v_k_4820_, 1);
                    v_v_4823_ = lean_array_fget_borrowed(v_vals_4815_, v_i_4816_);
                    v___x_4824_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4821_);
                    v___x_4825_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4822_);
                    v___x_4826_ = lean_uint64_mix_hash(v___x_4824_, v___x_4825_);
                    v_h_4827_ = lean_uint64_to_usize(v___x_4826_);
                    v___x_4828_ = 5usize;
                    v___x_4829_ = lean_unsigned_to_nat(1);
                    v___x_4830_ = 1usize;
                    v___x_4831_ = lean_usize_sub(v_depth_4813_, v___x_4830_);
                    v___x_4832_ = lean_usize_mul(v___x_4828_, v___x_4831_);
                    v_h_4833_ = lean_usize_shift_right(v_h_4827_, v___x_4832_);
                    v___x_4834_ = lean_nat_add(v_i_4816_, v___x_4829_);
                    lean_dec(v_i_4816_);
                    lean_inc(v_v_4823_);
                    lean_inc(v_k_4820_);
                    v___x_4835_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_entries_4817_, v_h_4833_, v_depth_4813_, v_k_4820_, v_v_4823_);
                    v_i_4816_ = v___x_4834_;
                    v_entries_4817_ = v___x_4835_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_4837_: *mut LeanObject,
    mut v_keys_4838_: *mut LeanObject,
    mut v_vals_4839_: *mut LeanObject,
    mut v_i_4840_: *mut LeanObject,
    mut v_entries_4841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4842_: usize = 0;
    let mut v_res_4843_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4842_ = lean_unbox_usize(v_depth_4837_);
    lean_dec(v_depth_4837_);
    v_res_4843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4842_, v_keys_4838_, v_vals_4839_, v_i_4840_, v_entries_4841_);
    lean_dec_ref(v_vals_4839_);
    lean_dec_ref(v_keys_4838_);
    return v_res_4843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(
    mut v_x_4844_: *mut LeanObject,
    mut v_x_4845_: *mut LeanObject,
    mut v_x_4846_: *mut LeanObject,
    mut v_x_4847_: *mut LeanObject,
    mut v_x_4848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2837__boxed_4849_: usize = 0;
    let mut v_x_2838__boxed_4850_: usize = 0;
    let mut v_res_4851_: *mut LeanObject = core::ptr::null_mut();
    v_x_2837__boxed_4849_ = lean_unbox_usize(v_x_4845_);
    lean_dec(v_x_4845_);
    v_x_2838__boxed_4850_ = lean_unbox_usize(v_x_4846_);
    lean_dec(v_x_4846_);
    v_res_4851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4844_, v_x_2837__boxed_4849_, v_x_2838__boxed_4850_, v_x_4847_, v_x_4848_);
    return v_res_4851_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(
    mut v_x_4852_: *mut LeanObject,
    mut v_x_4853_: *mut LeanObject,
    mut v_x_4854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: u64 = 0;
    let mut v___x_4858_: u64 = 0;
    let mut v___x_4859_: u64 = 0;
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: usize = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    v_fst_4855_ = lean_ctor_get(v_x_4853_, 0);
    v_snd_4856_ = lean_ctor_get(v_x_4853_, 1);
    v___x_4857_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4855_);
    v___x_4858_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4856_);
    v___x_4859_ = lean_uint64_mix_hash(v___x_4857_, v___x_4858_);
    v___x_4860_ = lean_uint64_to_usize(v___x_4859_);
    v___x_4861_ = 1usize;
    v___x_4862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4852_, v___x_4860_, v___x_4861_, v_x_4853_, v_x_4854_);
    return v___x_4862_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI___redArg(
    mut v_s_4863_: *mut LeanObject,
    mut v_t_4864_: *mut LeanObject,
    mut v_a_4865_: *mut LeanObject,
    mut v_a_4866_: *mut LeanObject,
    mut v_a_4867_: *mut LeanObject,
    mut v_a_4868_: *mut LeanObject,
    mut v_a_4869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4882_: u8 = 0;
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4899_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4871_ = lean_st_ref_get(v_a_4865_);
                v_defEqI_4872_ = lean_ctor_get(v___x_4871_, 6);
                lean_inc_ref(v_defEqI_4872_);
                lean_dec(v___x_4871_);
                lean_inc_ref(v_t_4864_);
                lean_inc_ref(v_s_4863_);
                v_key_4873_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_key_4873_, 0, v_s_4863_);
                lean_ctor_set(v_key_4873_, 1, v_t_4864_);
                v___x_4874_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4872_, v_key_4873_);
                lean_dec_ref(v_defEqI_4872_);
                if lean_obj_tag(v___x_4874_) == 1 {
                    lean_dec_ref_known(v_key_4873_, 2);
                    lean_dec_ref(v_t_4864_);
                    lean_dec_ref(v_s_4863_);
                    v_val_4875_ = lean_ctor_get(v___x_4874_, 0);
                    v_isSharedCheck_4882_ = (!lean_is_exclusive(v___x_4874_)) as u8;
                    if v_isSharedCheck_4882_ == 0 {
                        v___x_4877_ = v___x_4874_;
                        v_isShared_4878_ = v_isSharedCheck_4882_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4875_);
                        lean_dec(v___x_4874_);
                        v___x_4877_ = lean_box(0);
                        v_isShared_4878_ = v_isSharedCheck_4882_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4874_);
                    v___x_4883_ = l_Lean_Meta_isDefEqI(
                        v_s_4863_, v_t_4864_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_,
                    );
                    if lean_obj_tag(v___x_4883_) == 0 {
                        v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
                        v_isSharedCheck_4912_ = (!lean_is_exclusive(v___x_4883_)) as u8;
                        if v_isSharedCheck_4912_ == 0 {
                            v___x_4886_ = v___x_4883_;
                            v_isShared_4887_ = v_isSharedCheck_4912_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4884_);
                            lean_dec(v___x_4883_);
                            v___x_4886_ = lean_box(0);
                            v_isShared_4887_ = v_isSharedCheck_4912_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_key_4873_, 2);
                        return v___x_4883_;
                    }
                }
            }
            1 => {
                if v_isShared_4878_ == 0 {
                    lean_ctor_set_tag(v___x_4877_, 0);
                    v___x_4880_ = v___x_4877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_val_4875_);
                    v___x_4880_ = v_reuseFailAlloc_4881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4880_;
            }
            3 => {
                v___x_4888_ = lean_st_ref_take(v_a_4865_);
                v_share_4889_ = lean_ctor_get(v___x_4888_, 0);
                v_maxFVar_4890_ = lean_ctor_get(v___x_4888_, 1);
                v_proofInstInfo_4891_ = lean_ctor_get(v___x_4888_, 2);
                v_inferType_4892_ = lean_ctor_get(v___x_4888_, 3);
                v_getLevel_4893_ = lean_ctor_get(v___x_4888_, 4);
                v_congrInfo_4894_ = lean_ctor_get(v___x_4888_, 5);
                v_defEqI_4895_ = lean_ctor_get(v___x_4888_, 6);
                v_extensions_4896_ = lean_ctor_get(v___x_4888_, 7);
                v_issues_4897_ = lean_ctor_get(v___x_4888_, 8);
                v_canon_4898_ = lean_ctor_get(v___x_4888_, 9);
                v_debug_4899_ = lean_ctor_get_uint8(
                    v___x_4888_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4911_ = (!lean_is_exclusive(v___x_4888_)) as u8;
                if v_isSharedCheck_4911_ == 0 {
                    v___x_4901_ = v___x_4888_;
                    v_isShared_4902_ = v_isSharedCheck_4911_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_4898_);
                    lean_inc(v_issues_4897_);
                    lean_inc(v_extensions_4896_);
                    lean_inc(v_defEqI_4895_);
                    lean_inc(v_congrInfo_4894_);
                    lean_inc(v_getLevel_4893_);
                    lean_inc(v_inferType_4892_);
                    lean_inc(v_proofInstInfo_4891_);
                    lean_inc(v_maxFVar_4890_);
                    lean_inc(v_share_4889_);
                    lean_dec(v___x_4888_);
                    v___x_4901_ = lean_box(0);
                    v_isShared_4902_ = v_isSharedCheck_4911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_4884_);
                v___x_4903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4895_, v_key_4873_, v_a_4884_);
                if v_isShared_4902_ == 0 {
                    lean_ctor_set(v___x_4901_, 6, v___x_4903_);
                    v___x_4905_ = v___x_4901_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_share_4889_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_maxFVar_4890_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_proofInstInfo_4891_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_inferType_4892_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 4, v_getLevel_4893_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 5, v_congrInfo_4894_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 6, v___x_4903_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 7, v_extensions_4896_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 8, v_issues_4897_);
                    lean_ctor_set(v_reuseFailAlloc_4910_, 9, v_canon_4898_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4910_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4899_,
                    );
                    v___x_4905_ = v_reuseFailAlloc_4910_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4906_ = lean_st_ref_set(v_a_4865_, v___x_4905_);
                if v_isShared_4887_ == 0 {
                    v___x_4908_ = v___x_4886_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4884_);
                    v___x_4908_ = v_reuseFailAlloc_4909_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI___redArg___boxed(
    mut v_s_4913_: *mut LeanObject,
    mut v_t_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
    mut v_a_4920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4921_: *mut LeanObject = core::ptr::null_mut();
    v_res_4921_ = l_Lean_Meta_Sym_isDefEqI___redArg(
        v_s_4913_, v_t_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_,
    );
    lean_dec(v_a_4919_);
    lean_dec_ref(v_a_4918_);
    lean_dec(v_a_4917_);
    lean_dec_ref(v_a_4916_);
    lean_dec(v_a_4915_);
    return v_res_4921_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI(
    mut v_s_4922_: *mut LeanObject,
    mut v_t_4923_: *mut LeanObject,
    mut v_a_4924_: *mut LeanObject,
    mut v_a_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
    mut v_a_4927_: *mut LeanObject,
    mut v_a_4928_: *mut LeanObject,
    mut v_a_4929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    v___x_4931_ = l_Lean_Meta_Sym_isDefEqI___redArg(
        v_s_4922_, v_t_4923_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_,
    );
    return v___x_4931_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI___boxed(
    mut v_s_4932_: *mut LeanObject,
    mut v_t_4933_: *mut LeanObject,
    mut v_a_4934_: *mut LeanObject,
    mut v_a_4935_: *mut LeanObject,
    mut v_a_4936_: *mut LeanObject,
    mut v_a_4937_: *mut LeanObject,
    mut v_a_4938_: *mut LeanObject,
    mut v_a_4939_: *mut LeanObject,
    mut v_a_4940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4941_: *mut LeanObject = core::ptr::null_mut();
    v_res_4941_ = l_Lean_Meta_Sym_isDefEqI(
        v_s_4932_, v_t_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_,
    );
    lean_dec(v_a_4939_);
    lean_dec_ref(v_a_4938_);
    lean_dec(v_a_4937_);
    lean_dec_ref(v_a_4936_);
    lean_dec(v_a_4935_);
    lean_dec_ref(v_a_4934_);
    return v_res_4941_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(
    mut v_00_u03b2_4942_: *mut LeanObject,
    mut v_x_4943_: *mut LeanObject,
    mut v_x_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    v___x_4945_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
            v_x_4943_, v_x_4944_,
        );
    return v___x_4945_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(
    mut v_00_u03b2_4946_: *mut LeanObject,
    mut v_x_4947_: *mut LeanObject,
    mut v_x_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4949_: *mut LeanObject = core::ptr::null_mut();
    v_res_4949_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(
        v_00_u03b2_4946_,
        v_x_4947_,
        v_x_4948_,
    );
    lean_dec_ref(v_x_4948_);
    lean_dec_ref(v_x_4947_);
    return v_res_4949_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(
    mut v_00_u03b2_4950_: *mut LeanObject,
    mut v_x_4951_: *mut LeanObject,
    mut v_x_4952_: *mut LeanObject,
    mut v_x_4953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(
        v_x_4951_, v_x_4952_, v_x_4953_,
    );
    return v___x_4954_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(
    mut v_00_u03b2_4955_: *mut LeanObject,
    mut v_x_4956_: *mut LeanObject,
    mut v_x_4957_: usize,
    mut v_x_4958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    v___x_4959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4956_, v_x_4957_, v_x_4958_);
    return v___x_4959_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(
    mut v_00_u03b2_4960_: *mut LeanObject,
    mut v_x_4961_: *mut LeanObject,
    mut v_x_4962_: *mut LeanObject,
    mut v_x_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3116__boxed_4964_: usize = 0;
    let mut v_res_4965_: *mut LeanObject = core::ptr::null_mut();
    v_x_3116__boxed_4964_ = lean_unbox_usize(v_x_4962_);
    lean_dec(v_x_4962_);
    v_res_4965_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4960_, v_x_4961_, v_x_3116__boxed_4964_, v_x_4963_);
    lean_dec_ref(v_x_4963_);
    lean_dec_ref(v_x_4961_);
    return v_res_4965_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(
    mut v_00_u03b2_4966_: *mut LeanObject,
    mut v_x_4967_: *mut LeanObject,
    mut v_x_4968_: usize,
    mut v_x_4969_: usize,
    mut v_x_4970_: *mut LeanObject,
    mut v_x_4971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    v___x_4972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4967_, v_x_4968_, v_x_4969_, v_x_4970_, v_x_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(
    mut v_00_u03b2_4973_: *mut LeanObject,
    mut v_x_4974_: *mut LeanObject,
    mut v_x_4975_: *mut LeanObject,
    mut v_x_4976_: *mut LeanObject,
    mut v_x_4977_: *mut LeanObject,
    mut v_x_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3127__boxed_4979_: usize = 0;
    let mut v_x_3128__boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut LeanObject = core::ptr::null_mut();
    v_x_3127__boxed_4979_ = lean_unbox_usize(v_x_4975_);
    lean_dec(v_x_4975_);
    v_x_3128__boxed_4980_ = lean_unbox_usize(v_x_4976_);
    lean_dec(v_x_4976_);
    v_res_4981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4973_, v_x_4974_, v_x_3127__boxed_4979_, v_x_3128__boxed_4980_, v_x_4977_, v_x_4978_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4982_: *mut LeanObject,
    mut v_keys_4983_: *mut LeanObject,
    mut v_vals_4984_: *mut LeanObject,
    mut v_heq_4985_: *mut LeanObject,
    mut v_i_4986_: *mut LeanObject,
    mut v_k_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    v___x_4988_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4983_, v_vals_4984_, v_i_4986_, v_k_4987_);
    return v___x_4988_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4989_: *mut LeanObject,
    mut v_keys_4990_: *mut LeanObject,
    mut v_vals_4991_: *mut LeanObject,
    mut v_heq_4992_: *mut LeanObject,
    mut v_i_4993_: *mut LeanObject,
    mut v_k_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4995_: *mut LeanObject = core::ptr::null_mut();
    v_res_4995_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4989_, v_keys_4990_, v_vals_4991_, v_heq_4992_, v_i_4993_, v_k_4994_);
    lean_dec_ref(v_k_4994_);
    lean_dec_ref(v_vals_4991_);
    lean_dec_ref(v_keys_4990_);
    return v_res_4995_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4996_: *mut LeanObject,
    mut v_n_4997_: *mut LeanObject,
    mut v_k_4998_: *mut LeanObject,
    mut v_v_4999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    v___x_5000_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4997_, v_k_4998_, v_v_4999_);
    return v___x_5000_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5001_: *mut LeanObject,
    mut v_depth_5002_: usize,
    mut v_keys_5003_: *mut LeanObject,
    mut v_vals_5004_: *mut LeanObject,
    mut v_heq_5005_: *mut LeanObject,
    mut v_i_5006_: *mut LeanObject,
    mut v_entries_5007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    v___x_5008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_5002_, v_keys_5003_, v_vals_5004_, v_i_5006_, v_entries_5007_);
    return v___x_5008_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_5009_: *mut LeanObject,
    mut v_depth_5010_: *mut LeanObject,
    mut v_keys_5011_: *mut LeanObject,
    mut v_vals_5012_: *mut LeanObject,
    mut v_heq_5013_: *mut LeanObject,
    mut v_i_5014_: *mut LeanObject,
    mut v_entries_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5016_: usize = 0;
    let mut v_res_5017_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5016_ = lean_unbox_usize(v_depth_5010_);
    lean_dec(v_depth_5010_);
    v_res_5017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_5009_, v_depth_boxed_5016_, v_keys_5011_, v_vals_5012_, v_heq_5013_, v_i_5014_, v_entries_5015_);
    lean_dec_ref(v_vals_5012_);
    lean_dec_ref(v_keys_5011_);
    return v_res_5017_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_5018_: *mut LeanObject,
    mut v_x_5019_: *mut LeanObject,
    mut v_x_5020_: *mut LeanObject,
    mut v_x_5021_: *mut LeanObject,
    mut v_x_5022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_5019_, v_x_5020_, v_x_5021_, v_x_5022_);
    return v___x_5023_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0() -> *mut LeanObject {
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_instMonadEIO(lean_box(0));
    return v___x_5024_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1() -> *mut LeanObject {
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    v___x_5025_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0,
    );
    v___x_5026_ = l_StateRefT_x27_instMonad___redArg(v___x_5025_);
    return v___x_5026_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6() -> *mut LeanObject {
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5032_: *mut LeanObject = core::ptr::null_mut();
    v___x_5031_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_5032_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5032_, 0, v___x_5031_);
    return v___f_5032_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7() -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5034_: *mut LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_5034_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5034_, 0, v___x_5033_);
    return v___f_5034_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8() -> *mut LeanObject {
    let mut v___f_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    v___f_5035_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7,
    );
    v___f_5036_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6,
    );
    v___x_5037_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5037_, 0, v___f_5036_);
    lean_ctor_set(v___x_5037_, 1, v___f_5035_);
    return v___x_5037_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9() -> *mut LeanObject {
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5039_: *mut LeanObject = core::ptr::null_mut();
    v___x_5038_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8,
    );
    v___f_5039_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5039_, 0, v___x_5038_);
    return v___f_5039_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10() -> *mut LeanObject {
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut LeanObject = core::ptr::null_mut();
    v___x_5040_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8,
    );
    v___f_5041_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5041_, 0, v___x_5040_);
    return v___f_5041_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11() -> *mut LeanObject {
    let mut v___f_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    v___f_5042_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10,
    );
    v___f_5043_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9,
    );
    v___x_5044_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5044_, 0, v___f_5043_);
    lean_ctor_set(v___x_5044_, 1, v___f_5042_);
    return v___x_5044_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12() -> *mut LeanObject {
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5046_: *mut LeanObject = core::ptr::null_mut();
    v___x_5045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11,
    );
    v___f_5046_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5046_, 0, v___x_5045_);
    return v___f_5046_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13() -> *mut LeanObject {
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5048_: *mut LeanObject = core::ptr::null_mut();
    v___x_5047_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11,
    );
    v___f_5048_ = lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5048_, 0, v___x_5047_);
    return v___f_5048_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14() -> *mut LeanObject {
    let mut v___f_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    v___f_5049_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13,
    );
    v___f_5050_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12,
    );
    v___x_5051_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5051_, 0, v___f_5050_);
    lean_ctor_set(v___x_5051_, 1, v___f_5049_);
    return v___x_5051_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15() -> *mut LeanObject {
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5053_: *mut LeanObject = core::ptr::null_mut();
    v___x_5052_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14,
    );
    v___f_5053_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5053_, 0, v___x_5052_);
    return v___f_5053_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16() -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut LeanObject = core::ptr::null_mut();
    v___x_5054_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14,
    );
    v___f_5055_ = lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5055_, 0, v___x_5054_);
    return v___f_5055_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17() -> *mut LeanObject {
    let mut v___f_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    v___f_5056_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16,
    );
    v___f_5057_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15,
    );
    v___x_5058_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5058_, 0, v___f_5057_);
    lean_ctor_set(v___x_5058_, 1, v___f_5056_);
    return v___x_5058_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22() -> *mut LeanObject {
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    v___x_5063_ = l_Lean_Core_instMonadQuotationCoreM;
    v___x_5064_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
    v___x_5065_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__20;
    v___x_5066_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_5065_,
        v___x_5064_,
        v___x_5063_,
    );
    return v___x_5066_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23() -> *mut LeanObject {
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    v___x_5067_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22,
    );
    v___f_5068_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
    v___f_5069_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__18;
    v___x_5070_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_5069_,
        v___f_5068_,
        v___x_5067_,
    );
    return v___x_5070_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24() -> *mut LeanObject {
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    v___x_5071_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23,
    );
    v___x_5072_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
    v___x_5073_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__20;
    v___x_5074_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___x_5073_,
        v___x_5072_,
        v___x_5071_,
    );
    return v___x_5074_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25() -> *mut LeanObject {
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    v___x_5075_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24,
    );
    v___f_5076_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
    v___f_5077_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__18;
    v___x_5078_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(
        v___f_5077_,
        v___f_5076_,
        v___x_5075_,
    );
    return v___x_5078_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26() -> *mut LeanObject {
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5079_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
    v___x_5080_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_5081_ = lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5081_, 0, v___x_5080_);
    lean_closure_set(v___f_5081_, 1, v___x_5079_);
    return v___f_5081_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27() -> *mut LeanObject {
    let mut v___f_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5084_: *mut LeanObject = core::ptr::null_mut();
    v___f_5082_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
    v___f_5083_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26,
    );
    v___f_5084_ = lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5084_, 0, v___f_5083_);
    lean_closure_set(v___f_5084_, 1, v___f_5082_);
    return v___f_5084_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29() -> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__28;
    v___x_5087_ = l_Lean_stringToMessageData(v___x_5086_);
    return v___x_5087_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymM(
    mut v_00_u03b1_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v_toFunctor_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v___f_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5141_: u8 = 0;
    let mut v_unused_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_unused_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5089_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1,
                );
                v_toApplicative_5090_ = lean_ctor_get(v___x_5089_, 0);
                v_toFunctor_5091_ = lean_ctor_get(v_toApplicative_5090_, 0);
                v_toSeq_5092_ = lean_ctor_get(v_toApplicative_5090_, 2);
                v_toSeqLeft_5093_ = lean_ctor_get(v_toApplicative_5090_, 3);
                v_toSeqRight_5094_ = lean_ctor_get(v_toApplicative_5090_, 4);
                v___f_5095_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__2;
                v___f_5096_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__3;
                lean_inc_ref_n(v_toFunctor_5091_, 2);
                v___f_5097_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5097_, 0, v_toFunctor_5091_);
                v___f_5098_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5098_, 0, v_toFunctor_5091_);
                v___x_5099_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5099_, 0, v___f_5097_);
                lean_ctor_set(v___x_5099_, 1, v___f_5098_);
                lean_inc(v_toSeqRight_5094_);
                v___f_5100_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5100_, 0, v_toSeqRight_5094_);
                lean_inc(v_toSeqLeft_5093_);
                v___f_5101_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5101_, 0, v_toSeqLeft_5093_);
                lean_inc(v_toSeq_5092_);
                v___f_5102_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5102_, 0, v_toSeq_5092_);
                v___x_5103_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_5103_, 0, v___x_5099_);
                lean_ctor_set(v___x_5103_, 1, v___f_5095_);
                lean_ctor_set(v___x_5103_, 2, v___f_5102_);
                lean_ctor_set(v___x_5103_, 3, v___f_5101_);
                lean_ctor_set(v___x_5103_, 4, v___f_5100_);
                v___x_5104_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5104_, 0, v___x_5103_);
                lean_ctor_set(v___x_5104_, 1, v___f_5096_);
                v___x_5105_ = l_StateRefT_x27_instMonad___redArg(v___x_5104_);
                v_toApplicative_5106_ = lean_ctor_get(v___x_5105_, 0);
                v_isSharedCheck_5143_ = (!lean_is_exclusive(v___x_5105_)) as u8;
                if v_isSharedCheck_5143_ == 0 {
                    v_unused_5144_ = lean_ctor_get(v___x_5105_, 1);
                    lean_dec(v_unused_5144_);
                    v___x_5108_ = v___x_5105_;
                    v_isShared_5109_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_5106_);
                    lean_dec(v___x_5105_);
                    v___x_5108_ = lean_box(0);
                    v_isShared_5109_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5110_ = lean_ctor_get(v_toApplicative_5106_, 0);
                v_toSeq_5111_ = lean_ctor_get(v_toApplicative_5106_, 2);
                v_toSeqLeft_5112_ = lean_ctor_get(v_toApplicative_5106_, 3);
                v_toSeqRight_5113_ = lean_ctor_get(v_toApplicative_5106_, 4);
                v_isSharedCheck_5141_ = (!lean_is_exclusive(v_toApplicative_5106_)) as u8;
                if v_isSharedCheck_5141_ == 0 {
                    v_unused_5142_ = lean_ctor_get(v_toApplicative_5106_, 1);
                    lean_dec(v_unused_5142_);
                    v___x_5115_ = v_toApplicative_5106_;
                    v_isShared_5116_ = v_isSharedCheck_5141_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_5113_);
                    lean_inc(v_toSeqLeft_5112_);
                    lean_inc(v_toSeq_5111_);
                    lean_inc(v_toFunctor_5110_);
                    lean_dec(v_toApplicative_5106_);
                    v___x_5115_ = lean_box(0);
                    v_isShared_5116_ = v_isSharedCheck_5141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5117_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__4;
                v___f_5118_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__5;
                lean_inc_ref(v_toFunctor_5110_);
                v___f_5119_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5119_, 0, v_toFunctor_5110_);
                v___f_5120_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5120_, 0, v_toFunctor_5110_);
                v___x_5121_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5121_, 0, v___f_5119_);
                lean_ctor_set(v___x_5121_, 1, v___f_5120_);
                v___f_5122_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5122_, 0, v_toSeqRight_5113_);
                v___f_5123_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5123_, 0, v_toSeqLeft_5112_);
                v___f_5124_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_5124_, 0, v_toSeq_5111_);
                if v_isShared_5116_ == 0 {
                    lean_ctor_set(v___x_5115_, 4, v___f_5122_);
                    lean_ctor_set(v___x_5115_, 3, v___f_5123_);
                    lean_ctor_set(v___x_5115_, 2, v___f_5124_);
                    lean_ctor_set(v___x_5115_, 1, v___f_5117_);
                    lean_ctor_set(v___x_5115_, 0, v___x_5121_);
                    v___x_5126_ = v___x_5115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5140_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5121_);
                    lean_ctor_set(v_reuseFailAlloc_5140_, 1, v___f_5117_);
                    lean_ctor_set(v_reuseFailAlloc_5140_, 2, v___f_5124_);
                    lean_ctor_set(v_reuseFailAlloc_5140_, 3, v___f_5123_);
                    lean_ctor_set(v_reuseFailAlloc_5140_, 4, v___f_5122_);
                    v___x_5126_ = v_reuseFailAlloc_5140_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5109_ == 0 {
                    lean_ctor_set(v___x_5108_, 1, v___f_5118_);
                    lean_ctor_set(v___x_5108_, 0, v___x_5126_);
                    v___x_5128_ = v___x_5108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5126_);
                    lean_ctor_set(v_reuseFailAlloc_5139_, 1, v___f_5118_);
                    v___x_5128_ = v_reuseFailAlloc_5139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5129_ = l_StateRefT_x27_instMonad___redArg(v___x_5128_);
                v___x_5130_ = l_ReaderT_instMonad___redArg(v___x_5129_);
                v___x_5131_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17,
                );
                v___x_5132_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__25),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25,
                );
                v_toMonadRef_5133_ = lean_ctor_get(v___x_5132_, 0);
                v___f_5134_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__27),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27,
                );
                lean_inc_ref(v___x_5130_);
                v___x_5135_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_5134_,
                    v___x_5130_,
                );
                lean_inc_ref(v_toMonadRef_5133_);
                v___x_5136_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5136_, 0, v___x_5131_);
                lean_ctor_set(v___x_5136_, 1, v_toMonadRef_5133_);
                lean_ctor_set(v___x_5136_, 2, v___x_5135_);
                v___x_5137_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__29),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29,
                );
                v___x_5138_ = l_Lean_throwError___redArg(v___x_5130_, v___x_5136_, v___x_5137_);
                return v___x_5138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(
    mut v_ext_5145_: *mut LeanObject,
    mut v_extensions_5146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_id_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    v_id_5148_ = lean_ctor_get(v_ext_5145_, 0);
    v___x_5149_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
    v___x_5150_ = lean_array_get_borrowed(v___x_5149_, v_extensions_5146_, v_id_5148_);
    lean_inc(v___x_5150_);
    v___x_5151_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5151_, 0, v___x_5150_);
    return v___x_5151_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(
    mut v_ext_5152_: *mut LeanObject,
    mut v_extensions_5153_: *mut LeanObject,
    mut v_a_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5155_: *mut LeanObject = core::ptr::null_mut();
    v_res_5155_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(
            v_ext_5152_,
            v_extensions_5153_,
        );
    lean_dec_ref(v_extensions_5153_);
    lean_dec_ref(v_ext_5152_);
    return v_res_5155_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(
    mut v_00_u03c3_5156_: *mut LeanObject,
    mut v_ext_5157_: *mut LeanObject,
    mut v_extensions_5158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    v___x_5160_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(
            v_ext_5157_,
            v_extensions_5158_,
        );
    return v___x_5160_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(
    mut v_00_u03c3_5161_: *mut LeanObject,
    mut v_ext_5162_: *mut LeanObject,
    mut v_extensions_5163_: *mut LeanObject,
    mut v_a_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5165_: *mut LeanObject = core::ptr::null_mut();
    v_res_5165_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(
        v_00_u03c3_5161_,
        v_ext_5162_,
        v_extensions_5163_,
    );
    lean_dec_ref(v_extensions_5163_);
    lean_dec_ref(v_ext_5162_);
    return v_res_5165_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState___redArg(
    mut v_ext_5166_: *mut LeanObject,
    mut v_a_5167_: *mut LeanObject,
    mut v_a_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v_ref_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = lean_st_ref_get(v_a_5167_);
                v_extensions_5171_ = lean_ctor_get(v___x_5170_, 7);
                lean_inc_ref(v_extensions_5171_);
                lean_dec(v___x_5170_);
                v___x_5172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5166_, v_extensions_5171_);
                lean_dec_ref(v_extensions_5171_);
                if lean_obj_tag(v___x_5172_) == 0 {
                    v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
                    v_isSharedCheck_5180_ = (!lean_is_exclusive(v___x_5172_)) as u8;
                    if v_isSharedCheck_5180_ == 0 {
                        v___x_5175_ = v___x_5172_;
                        v_isShared_5176_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5173_);
                        lean_dec(v___x_5172_);
                        v___x_5175_ = lean_box(0);
                        v_isShared_5176_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5181_ = lean_ctor_get(v___x_5172_, 0);
                    v_isSharedCheck_5193_ = (!lean_is_exclusive(v___x_5172_)) as u8;
                    if v_isSharedCheck_5193_ == 0 {
                        v___x_5183_ = v___x_5172_;
                        v_isShared_5184_ = v_isSharedCheck_5193_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5181_);
                        lean_dec(v___x_5172_);
                        v___x_5183_ = lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5193_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5176_ == 0 {
                    v___x_5178_ = v___x_5175_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5178_;
            }
            3 => {
                v_ref_5185_ = lean_ctor_get(v_a_5168_, 5);
                v___x_5186_ = lean_io_error_to_string(v_a_5181_);
                v___x_5187_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5187_, 0, v___x_5186_);
                v___x_5188_ = l_Lean_MessageData_ofFormat(v___x_5187_);
                lean_inc(v_ref_5185_);
                v___x_5189_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5189_, 0, v_ref_5185_);
                lean_ctor_set(v___x_5189_, 1, v___x_5188_);
                if v_isShared_5184_ == 0 {
                    lean_ctor_set(v___x_5183_, 0, v___x_5189_);
                    v___x_5191_ = v___x_5183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___x_5189_);
                    v___x_5191_ = v_reuseFailAlloc_5192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5191_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState___redArg___boxed(
    mut v_ext_5194_: *mut LeanObject,
    mut v_a_5195_: *mut LeanObject,
    mut v_a_5196_: *mut LeanObject,
    mut v_a_5197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5198_: *mut LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5194_, v_a_5195_, v_a_5196_);
    lean_dec_ref(v_a_5196_);
    lean_dec(v_a_5195_);
    lean_dec_ref(v_ext_5194_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState(
    mut v_00_u03c3_5199_: *mut LeanObject,
    mut v_ext_5200_: *mut LeanObject,
    mut v_a_5201_: *mut LeanObject,
    mut v_a_5202_: *mut LeanObject,
    mut v_a_5203_: *mut LeanObject,
    mut v_a_5204_: *mut LeanObject,
    mut v_a_5205_: *mut LeanObject,
    mut v_a_5206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    v___x_5208_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5200_, v_a_5202_, v_a_5205_);
    return v___x_5208_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState___boxed(
    mut v_00_u03c3_5209_: *mut LeanObject,
    mut v_ext_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
    mut v_a_5217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5218_: *mut LeanObject = core::ptr::null_mut();
    v_res_5218_ = l_Lean_Meta_Sym_SymExtension_getState(
        v_00_u03c3_5209_,
        v_ext_5210_,
        v_a_5211_,
        v_a_5212_,
        v_a_5213_,
        v_a_5214_,
        v_a_5215_,
        v_a_5216_,
    );
    lean_dec(v_a_5216_);
    lean_dec_ref(v_a_5215_);
    lean_dec(v_a_5214_);
    lean_dec_ref(v_a_5213_);
    lean_dec(v_a_5212_);
    lean_dec_ref(v_a_5211_);
    lean_dec_ref(v_ext_5210_);
    return v_res_5218_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
    mut v_ext_5219_: *mut LeanObject,
    mut v_f_5220_: *mut LeanObject,
    mut v_a_5221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_5234_: u8 = 0;
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5237_: u8 = 0;
    let mut v_id_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v_v_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = lean_st_ref_take(v_a_5221_);
                v_share_5224_ = lean_ctor_get(v___x_5223_, 0);
                v_maxFVar_5225_ = lean_ctor_get(v___x_5223_, 1);
                v_proofInstInfo_5226_ = lean_ctor_get(v___x_5223_, 2);
                v_inferType_5227_ = lean_ctor_get(v___x_5223_, 3);
                v_getLevel_5228_ = lean_ctor_get(v___x_5223_, 4);
                v_congrInfo_5229_ = lean_ctor_get(v___x_5223_, 5);
                v_defEqI_5230_ = lean_ctor_get(v___x_5223_, 6);
                v_extensions_5231_ = lean_ctor_get(v___x_5223_, 7);
                v_issues_5232_ = lean_ctor_get(v___x_5223_, 8);
                v_canon_5233_ = lean_ctor_get(v___x_5223_, 9);
                v_debug_5234_ = lean_ctor_get_uint8(
                    v___x_5223_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5253_ = (!lean_is_exclusive(v___x_5223_)) as u8;
                if v_isSharedCheck_5253_ == 0 {
                    v___x_5236_ = v___x_5223_;
                    v_isShared_5237_ = v_isSharedCheck_5253_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_5233_);
                    lean_inc(v_issues_5232_);
                    lean_inc(v_extensions_5231_);
                    lean_inc(v_defEqI_5230_);
                    lean_inc(v_congrInfo_5229_);
                    lean_inc(v_getLevel_5228_);
                    lean_inc(v_inferType_5227_);
                    lean_inc(v_proofInstInfo_5226_);
                    lean_inc(v_maxFVar_5225_);
                    lean_inc(v_share_5224_);
                    lean_dec(v___x_5223_);
                    v___x_5236_ = lean_box(0);
                    v_isShared_5237_ = v_isSharedCheck_5253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5238_ = lean_ctor_get(v_ext_5219_, 0);
                v___x_5239_ = lean_box(0);
                v___x_5247_ = lean_array_get_size(v_extensions_5231_);
                v___x_5248_ = lean_nat_dec_lt(v_id_5238_, v___x_5247_);
                if v___x_5248_ == 0 {
                    lean_dec(v_f_5220_);
                    v___y_5241_ = v_extensions_5231_;
                    state = 2;
                    continue;
                } else {
                    v_v_5249_ = lean_array_fget(v_extensions_5231_, v_id_5238_);
                    v_xs_x27_5250_ = lean_array_fset(v_extensions_5231_, v_id_5238_, v___x_5239_);
                    v___x_5251_ = lean_apply_1(v_f_5220_, v_v_5249_);
                    v___x_5252_ = lean_array_fset(v_xs_x27_5250_, v_id_5238_, v___x_5251_);
                    v___y_5241_ = v___x_5252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5237_ == 0 {
                    lean_ctor_set(v___x_5236_, 7, v___y_5241_);
                    v___x_5243_ = v___x_5236_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_share_5224_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_maxFVar_5225_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_proofInstInfo_5226_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_inferType_5227_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 4, v_getLevel_5228_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 5, v_congrInfo_5229_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 6, v_defEqI_5230_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 7, v___y_5241_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 8, v_issues_5232_);
                    lean_ctor_set(v_reuseFailAlloc_5246_, 9, v_canon_5233_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5246_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_5234_,
                    );
                    v___x_5243_ = v_reuseFailAlloc_5246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5244_ = lean_st_ref_set(v_a_5221_, v___x_5243_);
                v___x_5245_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5245_, 0, v___x_5239_);
                return v___x_5245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(
    mut v_ext_5254_: *mut LeanObject,
    mut v_f_5255_: *mut LeanObject,
    mut v_a_5256_: *mut LeanObject,
    mut v_a_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5258_: *mut LeanObject = core::ptr::null_mut();
    v_res_5258_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v_ext_5254_,
            v_f_5255_,
            v_a_5256_,
        );
    lean_dec(v_a_5256_);
    lean_dec_ref(v_ext_5254_);
    return v_res_5258_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(
    mut v_00_u03c3_5259_: *mut LeanObject,
    mut v_ext_5260_: *mut LeanObject,
    mut v_f_5261_: *mut LeanObject,
    mut v_a_5262_: *mut LeanObject,
    mut v_a_5263_: *mut LeanObject,
    mut v_a_5264_: *mut LeanObject,
    mut v_a_5265_: *mut LeanObject,
    mut v_a_5266_: *mut LeanObject,
    mut v_a_5267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    v___x_5269_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v_ext_5260_,
            v_f_5261_,
            v_a_5263_,
        );
    return v___x_5269_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(
    mut v_00_u03c3_5270_: *mut LeanObject,
    mut v_ext_5271_: *mut LeanObject,
    mut v_f_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
    mut v_a_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
    mut v_a_5279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5280_: *mut LeanObject = core::ptr::null_mut();
    v_res_5280_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(
        v_00_u03c3_5270_,
        v_ext_5271_,
        v_f_5272_,
        v_a_5273_,
        v_a_5274_,
        v_a_5275_,
        v_a_5276_,
        v_a_5277_,
        v_a_5278_,
    );
    lean_dec(v_a_5278_);
    lean_dec_ref(v_a_5277_);
    lean_dec(v_a_5276_);
    lean_dec_ref(v_a_5275_);
    lean_dec(v_a_5274_);
    lean_dec_ref(v_a_5273_);
    lean_dec_ref(v_ext_5271_);
    return v_res_5280_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_sym_debug = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Sym_sym_debug);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Sym_instInhabitedSymExtensionState =
        _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState();
    lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedSymExtensionState);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef =
        lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef);
    lean_dec_ref(res);
    l_Lean_Meta_Sym_instInhabitedConfig_default =
        _init_l_Lean_Meta_Sym_instInhabitedConfig_default();
    l_Lean_Meta_Sym_instInhabitedConfig = _init_l_Lean_Meta_Sym_instInhabitedConfig();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_SymM(builtin);
}
