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
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16563840882919605222 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12705026313358803449 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 104, 101, 99, 107, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17711119471907869950 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6218173260972607057 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_sym_debug: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 115, 117, 101, 115, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16563840882919605222 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13379912757096045311 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__3_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4607919608188261591 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 121, 109, 77, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16875470911029737534 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,11726973394908900231 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__9_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1267766208074481146 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__10_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5379550515515746046 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__11_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2529073834662971127 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__12_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__13_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2398512038427916102 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__14_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__15_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6594316647550557687 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__16_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5876541111662122634 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__17_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4903966020297646382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__18_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12573723659802585063 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__19_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3401488681846805806 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_SymExtensionStateSpec: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_SymExtensionStateSpec___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedSymExtensionState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value:
    crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 92,
    m_capacity: 92,
    m_length: 91,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32,
        96, 83, 121, 109, 96, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 44, 32, 101, 120,
        116, 101, 110, 115, 105, 111, 110, 115, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98,
        101, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 100, 117, 114, 105, 110,
        103, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstArgInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value:
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
static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedProofInstInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_instInhabitedConfig_default: u8 = 0;
pub static mut l_Lean_Meta_Sym_instInhabitedConfig: u8 = 0;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        907667957179513571 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        11870096045526947150 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__7_value
        ) as *mut crate::leanh::LeanObject,
        15761733860085307253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__14_value
        ) as *mut crate::leanh::LeanObject,
        5208578977668345058 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        5594775977794639463 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_SymM_run___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_reportIssue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17036113238723837529 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_reportIssue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_reportIssue___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_reportIssue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_reportIssue___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Sym_reportIssue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_reportIssue___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__3_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_reportIssue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_reportIssue___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_reportIssue___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_reportIssue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__2_value) as *mut crate::leanh::LeanObject,5573444893818005634 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__4_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [83, 121, 109, 46, 114, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 73, 102, 86, 101, 114, 98, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [114, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 73, 102, 86, 101, 114, 98, 111, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12237061437965074038 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value) as *mut crate::leanh::LeanObject,11405738229328456530 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__8_value) as *mut crate::leanh::LeanObject,2994568011185431995 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__13_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__15_value) as *mut crate::leanh::LeanObject,14298422259736409839 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__17_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__1_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__19_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__22_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__25_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__26_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value) as *mut crate::leanh::LeanObject,11510953549444071797 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29_value) as *mut crate::leanh::LeanObject,491622604497152460 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__34_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__33_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__35_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 101, 114, 109, 77, 33, 95, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__38_value) as *mut crate::leanh::LeanObject,13317951319906582257 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 33, 0]};
static mut l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        100, 111, 69, 108, 101, 109, 82, 101, 112, 111, 114, 116, 73, 115, 115, 117, 101, 33, 95,
        95, 0,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        3146137996699014428 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__2_value)
            as *mut crate::leanh::LeanObject,
        12571085391447129896 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value:
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
    m_data: [111, 114, 101, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__6_value)
            as *mut crate::leanh::LeanObject,
        393173242845875278 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__8_value)
            as *mut crate::leanh::LeanObject,
        18163029821153688220 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__10_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__11_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_doElemReportIssue_x21____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,12237061437965074038 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4429398455170599012 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18355236360871851557 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        100, 111, 69, 108, 101, 109, 82, 101, 112, 111, 114, 116, 68, 98, 103, 73, 115, 115, 117,
        101, 33, 95, 95, 0,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__5_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__6_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__7_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,4034176598647545331 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__0_value)
            as *mut crate::leanh::LeanObject,
        5603533687169962240 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1022 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Sym_doElemReportDbgIssue_x21____: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_instMonadFunctor___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__21_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value: crate::leanh::LeanStringObject<
    21,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        60, 83, 121, 109, 77, 32, 100, 101, 102, 97, 117, 108, 116, 32, 118, 97, 108, 117, 101, 62,
        0,
    ],
};
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instInhabitedSymM___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instInhabitedSymM___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(
    mut v_name_2641_: *mut crate::leanh::LeanObject,
    mut v_decl_2642_: *mut crate::leanh::LeanObject,
    mut v_ref_2643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_unused_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2645_ = crate::leanh::lean_ctor_get(v_decl_2642_, 0);
                v_descr_2646_ = crate::leanh::lean_ctor_get(v_decl_2642_, 1);
                v_deprecation_x3f_2647_ = crate::leanh::lean_ctor_get(v_decl_2642_, 2);
                v___x_2648_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2649_ = (crate::leanh::lean_unbox(v_defValue_2645_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_2648_, 0 as u32, v___x_2649_);
                crate::leanh::lean_inc(v_deprecation_x3f_2647_);
                crate::leanh::lean_inc_ref(v_descr_2646_);
                crate::leanh::lean_inc_n(v_name_2641_, 2);
                v___x_2650_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2650_, 0, v_name_2641_);
                crate::leanh::lean_ctor_set(v___x_2650_, 1, v_ref_2643_);
                crate::leanh::lean_ctor_set(v___x_2650_, 2, v___x_2648_);
                crate::leanh::lean_ctor_set(v___x_2650_, 3, v_descr_2646_);
                crate::leanh::lean_ctor_set(v___x_2650_, 4, v_deprecation_x3f_2647_);
                v___x_2651_ = lean_register_option(v_name_2641_, v___x_2650_);
                if crate::leanh::lean_obj_tag(v___x_2651_) == 0 {
                    v_isSharedCheck_2659_ = (!crate::leanh::lean_is_exclusive(v___x_2651_)) as u8;
                    if v_isSharedCheck_2659_ == 0 {
                        v_unused_2660_ = crate::leanh::lean_ctor_get(v___x_2651_, 0);
                        crate::leanh::lean_dec(v_unused_2660_);
                        v___x_2653_ = v___x_2651_;
                        v_isShared_2654_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2651_);
                        v___x_2653_ = crate::leanh::lean_box(0);
                        v_isShared_2654_ = v_isSharedCheck_2659_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2641_);
                    v_a_2661_ = crate::leanh::lean_ctor_get(v___x_2651_, 0);
                    v_isSharedCheck_2668_ = (!crate::leanh::lean_is_exclusive(v___x_2651_)) as u8;
                    if v_isSharedCheck_2668_ == 0 {
                        v___x_2663_ = v___x_2651_;
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2661_);
                        crate::leanh::lean_dec(v___x_2651_);
                        v___x_2663_ = crate::leanh::lean_box(0);
                        v_isShared_2664_ = v_isSharedCheck_2668_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_2645_);
                v___x_2655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v_name_2641_);
                crate::leanh::lean_ctor_set(v___x_2655_, 1, v_defValue_2645_);
                if v_isShared_2654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2653_, 0, v___x_2655_);
                    v___x_2657_ = v___x_2653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
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
                    v_reuseFailAlloc_2667_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
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
    mut v_name_2669_: *mut crate::leanh::LeanObject,
    mut v_decl_2670_: *mut crate::leanh::LeanObject,
    mut v_ref_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2673_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v_name_2669_, v_decl_2670_, v_ref_2671_);
    crate::leanh::lean_dec_ref(v_decl_2670_);
    return v_res_2673_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__2_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2696_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__4_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2697_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__8_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_;
    v___x_2698_ = l_Lean_Option_register___at___00__private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4__spec__0(v___x_2695_, v___x_2696_, v___x_2697_);
    return v___x_2698_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4____boxed(
    mut v_a_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2700_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
    return v_res_2700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = crate::leanh::lean_unsigned_to_nat(2410647589);
    v___x_2755_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__20_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2756_ = l_Lean_Name_num___override(v___x_2755_, v___x_2754_);
    return v___x_2756_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2758_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__22_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__21_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2760_ = l_Lean_Name_str___override(v___x_2759_, v___x_2758_);
    return v___x_2760_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2762_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__24_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2763_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__23_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2764_ = l_Lean_Name_str___override(v___x_2763_, v___x_2762_);
    return v___x_2764_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2765_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__25_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2767_ = l_Lean_Name_num___override(v___x_2766_, v___x_2765_);
    return v___x_2767_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_2770_ = 0;
    v___x_2771_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__26_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_);
    v___x_2772_ = l_Lean_registerTraceClass(v___x_2769_, v___x_2770_, v___x_2771_);
    return v___x_2772_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2____boxed(
    mut v_a_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
    return v_res_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2778_ = l_Lean_Meta_Sym_SymExtensionStateSpec;
    v_snd_2779_ = crate::leanh::lean_ctor_get(v___x_2778_, 1);
    crate::leanh::lean_inc(v_snd_2779_);
    return v_snd_2779_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2784_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___closed__1;
    v___x_2785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2785_, 0, v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0___boxed(
    mut v___y_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___lam__0();
    return v_res_2787_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension_default(
    mut v_00_u03c3_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2793_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default___closed__1;
    return v___x_2793_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_Meta_Sym_instInhabitedSymExtension_default(crate::leanh::lean_box(0));
    return v___x_2794_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymExtension(
    mut v_a_2795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymExtension___closed__0,
    );
    return v___x_2796_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__0_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_;
    v___x_2801_ = lean_st_mk_ref(v___x_2800_);
    v___x_2802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2802_, 0, v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2____boxed(
    mut v_a_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2804_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
    return v_res_2804_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(
    mut v_ext_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_ext_2805_);
    return v_ext_2805_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg___boxed(
    mut v_ext_2806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2807_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___redArg(
            v_ext_2806_,
        );
    crate::leanh::lean_dec_ref(v_ext_2806_);
    return v_res_2807_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(
    mut v_00_u03c3_2808_: *mut crate::leanh::LeanObject,
    mut v_ext_2809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_ext_2809_);
    return v_ext_2809_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1___boxed(
    mut v_00_u03c3_2810_: *mut crate::leanh::LeanObject,
    mut v_ext_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_registerSymExtension_unsafe__1(
        v_00_u03c3_2810_,
        v_ext_2811_,
    );
    crate::leanh::lean_dec_ref(v_ext_2811_);
    return v_res_2812_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2814_ = l_Lean_Meta_Sym_registerSymExtension___redArg___closed__0;
    v___x_2815_ = lean_mk_io_user_error(v___x_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension___redArg(
    mut v_mkInitial_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2838_: u8 = 0;
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2818_ = l_Lean_initializing();
                if crate::leanh::lean_obj_tag(v___x_2818_) == 0 {
                    v_a_2819_ = crate::leanh::lean_ctor_get(v___x_2818_, 0);
                    v_isSharedCheck_2838_ = (!crate::leanh::lean_is_exclusive(v___x_2818_)) as u8;
                    if v_isSharedCheck_2838_ == 0 {
                        v___x_2821_ = v___x_2818_;
                        v_isShared_2822_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2819_);
                        crate::leanh::lean_dec(v___x_2818_);
                        v___x_2821_ = crate::leanh::lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2838_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mkInitial_2816_);
                    v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2818_, 0);
                    v_isSharedCheck_2846_ = (!crate::leanh::lean_is_exclusive(v___x_2818_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v___x_2841_ = v___x_2818_;
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2839_);
                        crate::leanh::lean_dec(v___x_2818_);
                        v___x_2841_ = crate::leanh::lean_box(0);
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2823_ = (crate::leanh::lean_unbox(v_a_2819_) as u8);
                crate::leanh::lean_dec(v_a_2819_);
                if v___x_2823_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInitial_2816_);
                    v___x_2824_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_registerSymExtension___redArg___closed__1,
                    );
                    if v_isShared_2822_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2821_, 1);
                        crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2824_);
                        v___x_2826_ = v___x_2821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2828_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
                    v___x_2829_ = lean_st_ref_get(v___x_2828_);
                    v___x_2830_ = lean_st_ref_take(v___x_2828_);
                    v___x_2831_ = lean_array_get_size(v___x_2829_);
                    crate::leanh::lean_dec(v___x_2829_);
                    v___x_2832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2832_, 0, v___x_2831_);
                    crate::leanh::lean_ctor_set(v___x_2832_, 1, v_mkInitial_2816_);
                    crate::leanh::lean_inc_ref(v___x_2832_);
                    v___x_2833_ = lean_array_push(v___x_2830_, v___x_2832_);
                    v___x_2834_ = lean_st_ref_set(v___x_2828_, v___x_2833_);
                    if v_isShared_2822_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2832_);
                        v___x_2836_ = v___x_2821_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2832_);
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
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
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
    mut v_mkInitial_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension(
    mut v_00_u03c3_2850_: *mut crate::leanh::LeanObject,
    mut v_mkInitial_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_Meta_Sym_registerSymExtension___redArg(v_mkInitial_2851_);
    return v___x_2853_;
}
pub unsafe fn l_Lean_Meta_Sym_registerSymExtension___boxed(
    mut v_00_u03c3_2854_: *mut crate::leanh::LeanObject,
    mut v_mkInitial_2855_: *mut crate::leanh::LeanObject,
    mut v_a_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2857_ = l_Lean_Meta_Sym_registerSymExtension(v_00_u03c3_2854_, v_mkInitial_2855_);
    return v_res_2857_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(
    mut v_sz_2858_: usize,
    mut v_i_2859_: usize,
    mut v_bs_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mkInitial_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: usize = 0;
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2877_: u8 = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2862_ = lean_usize_dec_lt(v_i_2859_, v_sz_2858_);
                if v___x_2862_ == 0 {
                    v___x_2863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2863_, 0, v_bs_2860_);
                    return v___x_2863_;
                } else {
                    v_v_2864_ = lean_array_uget_borrowed(v_bs_2860_, v_i_2859_);
                    v_mkInitial_2865_ = crate::leanh::lean_ctor_get(v_v_2864_, 1);
                    crate::leanh::lean_inc_ref(v_mkInitial_2865_);
                    v___x_2866_ =
                        crate::leanh::lean_apply_1(v_mkInitial_2865_, crate::leanh::lean_box(0));
                    if crate::leanh::lean_obj_tag(v___x_2866_) == 0 {
                        v_a_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                        crate::leanh::lean_inc(v_a_2867_);
                        crate::leanh::lean_dec_ref_known(v___x_2866_, 1);
                        v___x_2868_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2869_ = lean_array_uset(v_bs_2860_, v_i_2859_, v___x_2868_);
                        v___x_2870_ = 1usize;
                        v___x_2871_ = lean_usize_add(v_i_2859_, v___x_2870_);
                        v___x_2872_ = lean_array_uset(v_bs_x27_2869_, v_i_2859_, v_a_2867_);
                        v_i_2859_ = v___x_2871_;
                        v_bs_2860_ = v___x_2872_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2860_);
                        v_a_2874_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                        v_isSharedCheck_2881_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2866_)) as u8;
                        if v_isSharedCheck_2881_ == 0 {
                            v___x_2876_ = v___x_2866_;
                            v_isShared_2877_ = v_isSharedCheck_2881_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2874_);
                            crate::leanh::lean_dec(v___x_2866_);
                            v___x_2876_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
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
    mut v_sz_2882_: *mut crate::leanh::LeanObject,
    mut v_i_2883_: *mut crate::leanh::LeanObject,
    mut v_bs_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2886_: usize = 0;
    let mut v_i_boxed_2887_: usize = 0;
    let mut v_res_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2886_ = crate::leanh::lean_unbox_usize(v_sz_2882_);
    crate::leanh::lean_dec(v_sz_2882_);
    v_i_boxed_2887_ = crate::leanh::lean_unbox_usize(v_i_2883_);
    crate::leanh::lean_dec(v_i_2883_);
    v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_boxed_2886_, v_i_boxed_2887_, v_bs_2884_);
    return v_res_2888_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtensions_mkInitialStates() -> *mut crate::leanh::LeanObject {
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2892_: usize = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2890_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef;
    v___x_2891_ = lean_st_ref_get(v___x_2890_);
    v_sz_2892_ = lean_array_size(v___x_2891_);
    v___x_2893_ = 0usize;
    v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Sym_SymExtensions_mkInitialStates_spec__0(v_sz_2892_, v___x_2893_, v___x_2891_);
    return v___x_2894_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtensions_mkInitialStates___boxed(
    mut v_a_2895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2896_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
    return v_res_2896_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorIdx(
    mut v_x_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2905_) {
        0 => {
            let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2906_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2906_;
        }
        1 => {
            let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2907_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2907_;
        }
        2 => {
            let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2908_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2908_;
        }
        _ => {
            let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2909_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2909_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorIdx___boxed(
    mut v_x_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_Lean_Meta_Sym_CongrInfo_ctorIdx(v_x_2910_);
    crate::leanh::lean_dec(v_x_2910_);
    return v_res_2911_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(
    mut v_t_2912_: *mut crate::leanh::LeanObject,
    mut v_k_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2912_) {
        0 => {
            return v_k_2913_;
        }
        1 => {
            let mut v_prefixSize_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_suffixSize_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_prefixSize_2914_ = crate::leanh::lean_ctor_get(v_t_2912_, 0);
            crate::leanh::lean_inc(v_prefixSize_2914_);
            v_suffixSize_2915_ = crate::leanh::lean_ctor_get(v_t_2912_, 1);
            crate::leanh::lean_inc(v_suffixSize_2915_);
            crate::leanh::lean_dec_ref_known(v_t_2912_, 2);
            v___x_2916_ =
                crate::leanh::lean_apply_2(v_k_2913_, v_prefixSize_2914_, v_suffixSize_2915_);
            return v___x_2916_;
        }
        _ => {
            let mut v_rewritable_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_rewritable_2917_ = crate::leanh::lean_ctor_get(v_t_2912_, 0);
            crate::leanh::lean_inc_ref(v_rewritable_2917_);
            crate::leanh::lean_dec(v_t_2912_);
            v___x_2918_ = crate::leanh::lean_apply_1(v_k_2913_, v_rewritable_2917_);
            return v___x_2918_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim(
    mut v_motive_2919_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2920_: *mut crate::leanh::LeanObject,
    mut v_t_2921_: *mut crate::leanh::LeanObject,
    mut v_h_2922_: *mut crate::leanh::LeanObject,
    mut v_k_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2924_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2921_, v_k_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_ctorElim___boxed(
    mut v_motive_2925_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2926_: *mut crate::leanh::LeanObject,
    mut v_t_2927_: *mut crate::leanh::LeanObject,
    mut v_h_2928_: *mut crate::leanh::LeanObject,
    mut v_k_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Lean_Meta_Sym_CongrInfo_ctorElim(
        v_motive_2925_,
        v_ctorIdx_2926_,
        v_t_2927_,
        v_h_2928_,
        v_k_2929_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2926_);
    return v_res_2930_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_none_elim___redArg(
    mut v_t_2931_: *mut crate::leanh::LeanObject,
    mut v_none_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2933_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2931_, v_none_2932_);
    return v___x_2933_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_none_elim(
    mut v_motive_2934_: *mut crate::leanh::LeanObject,
    mut v_t_2935_: *mut crate::leanh::LeanObject,
    mut v_h_2936_: *mut crate::leanh::LeanObject,
    mut v_none_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2938_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2935_, v_none_2937_);
    return v___x_2938_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim___redArg(
    mut v_t_2939_: *mut crate::leanh::LeanObject,
    mut v_fixedPrefix_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2939_, v_fixedPrefix_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_fixedPrefix_elim(
    mut v_motive_2942_: *mut crate::leanh::LeanObject,
    mut v_t_2943_: *mut crate::leanh::LeanObject,
    mut v_h_2944_: *mut crate::leanh::LeanObject,
    mut v_fixedPrefix_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2946_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2943_, v_fixedPrefix_2945_);
    return v___x_2946_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_interlaced_elim___redArg(
    mut v_t_2947_: *mut crate::leanh::LeanObject,
    mut v_interlaced_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2949_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2947_, v_interlaced_2948_);
    return v___x_2949_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_interlaced_elim(
    mut v_motive_2950_: *mut crate::leanh::LeanObject,
    mut v_t_2951_: *mut crate::leanh::LeanObject,
    mut v_h_2952_: *mut crate::leanh::LeanObject,
    mut v_interlaced_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2951_, v_interlaced_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim___redArg(
    mut v_t_2955_: *mut crate::leanh::LeanObject,
    mut v_congrTheorem_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2957_ = l_Lean_Meta_Sym_CongrInfo_ctorElim___redArg(v_t_2955_, v_congrTheorem_2956_);
    return v___x_2957_;
}
pub unsafe fn l_Lean_Meta_Sym_CongrInfo_congrTheorem_elim(
    mut v_motive_2958_: *mut crate::leanh::LeanObject,
    mut v_t_2959_: *mut crate::leanh::LeanObject,
    mut v_h_2960_: *mut crate::leanh::LeanObject,
    mut v_congrTheorem_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = crate::leanh::lean_box(0);
    v___x_2969_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__1;
    v___x_2970_ = l_Lean_mkConst(v___x_2969_, v___x_2968_);
    return v___x_2970_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2974_ = crate::leanh::lean_box(0);
    v___x_2975_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__4;
    v___x_2976_ = l_Lean_mkConst(v___x_2975_, v___x_2974_);
    return v___x_2976_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2982_ = crate::leanh::lean_box(0);
    v___x_2983_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__8;
    v___x_2984_ = l_Lean_mkConst(v___x_2983_, v___x_2982_);
    return v___x_2984_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = crate::leanh::lean_box(0);
    v___x_2990_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__11;
    v___x_2991_ = l_Lean_mkConst(v___x_2990_, v___x_2989_);
    return v___x_2991_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2993_ = l_Lean_mkNatLit(v___x_2992_);
    return v___x_2993_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2999_ = crate::leanh::lean_box(0);
    v___x_3000_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__16;
    v___x_3001_ = l_Lean_mkConst(v___x_3000_, v___x_2999_);
    return v___x_3001_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(
    mut v_a_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3003_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__2);
                v___x_3004_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3003_, v_a_3002_);
                v_fst_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                crate::leanh::lean_inc(v_fst_3005_);
                v_snd_3006_ = crate::leanh::lean_ctor_get(v___x_3004_, 1);
                crate::leanh::lean_inc(v_snd_3006_);
                crate::leanh::lean_dec_ref(v___x_3004_);
                v___x_3007_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__5);
                v___x_3008_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3007_, v_snd_3006_);
                v_fst_3009_ = crate::leanh::lean_ctor_get(v___x_3008_, 0);
                crate::leanh::lean_inc(v_fst_3009_);
                v_snd_3010_ = crate::leanh::lean_ctor_get(v___x_3008_, 1);
                crate::leanh::lean_inc(v_snd_3010_);
                crate::leanh::lean_dec_ref(v___x_3008_);
                v___x_3011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__9);
                v___x_3012_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3011_, v_snd_3010_);
                v_fst_3013_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
                crate::leanh::lean_inc(v_fst_3013_);
                v_snd_3014_ = crate::leanh::lean_ctor_get(v___x_3012_, 1);
                crate::leanh::lean_inc(v_snd_3014_);
                crate::leanh::lean_dec_ref(v___x_3012_);
                v___x_3015_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__12);
                v___x_3016_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3015_, v_snd_3014_);
                v_fst_3017_ = crate::leanh::lean_ctor_get(v___x_3016_, 0);
                crate::leanh::lean_inc(v_fst_3017_);
                v_snd_3018_ = crate::leanh::lean_ctor_get(v___x_3016_, 1);
                crate::leanh::lean_inc(v_snd_3018_);
                crate::leanh::lean_dec_ref(v___x_3016_);
                v___x_3019_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__13);
                v___x_3020_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3019_, v_snd_3018_);
                v_fst_3021_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                crate::leanh::lean_inc(v_fst_3021_);
                v_snd_3022_ = crate::leanh::lean_ctor_get(v___x_3020_, 1);
                crate::leanh::lean_inc(v_snd_3022_);
                crate::leanh::lean_dec_ref(v___x_3020_);
                v___x_3023_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs___closed__17);
                v___x_3024_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3023_, v_snd_3022_);
                v_fst_3025_ = crate::leanh::lean_ctor_get(v___x_3024_, 0);
                crate::leanh::lean_inc(v_fst_3025_);
                v_snd_3026_ = crate::leanh::lean_ctor_get(v___x_3024_, 1);
                crate::leanh::lean_inc(v_snd_3026_);
                crate::leanh::lean_dec_ref(v___x_3024_);
                v___x_3027_ = l_Lean_Int_mkType;
                v___x_3028_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_shareCommonAlphaInc_go(v___x_3027_, v_snd_3026_);
                v_fst_3029_ = crate::leanh::lean_ctor_get(v___x_3028_, 0);
                v_snd_3030_ = crate::leanh::lean_ctor_get(v___x_3028_, 1);
                v_isSharedCheck_3038_ = (!crate::leanh::lean_is_exclusive(v___x_3028_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v___x_3032_ = v___x_3028_;
                    v_isShared_3033_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3030_);
                    crate::leanh::lean_inc(v_fst_3029_);
                    crate::leanh::lean_dec(v___x_3028_);
                    v___x_3032_ = crate::leanh::lean_box(0);
                    v_isShared_3033_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3034_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3034_, 0, v_fst_3009_);
                crate::leanh::lean_ctor_set(v___x_3034_, 1, v_fst_3005_);
                crate::leanh::lean_ctor_set(v___x_3034_, 2, v_fst_3021_);
                crate::leanh::lean_ctor_set(v___x_3034_, 3, v_fst_3017_);
                crate::leanh::lean_ctor_set(v___x_3034_, 4, v_fst_3013_);
                crate::leanh::lean_ctor_set(v___x_3034_, 5, v_fst_3025_);
                crate::leanh::lean_ctor_set(v___x_3034_, 6, v_fst_3029_);
                if v_isShared_3033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3032_, 0, v___x_3034_);
                    v___x_3036_ = v___x_3032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_snd_3030_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3039_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0_once
        ),
        _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0___closed__0,
    );
    v___x_3041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3041_, 0, v___x_3040_);
    return v___x_3041_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(
    mut v_00_u03b2_3042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = crate::leanh::lean_obj_once(
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
    mut v_opts_3044_: *mut crate::leanh::LeanObject,
    mut v_opt_3045_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3046_ = crate::leanh::lean_ctor_get(v_opt_3045_, 0);
    v_defValue_3047_ = crate::leanh::lean_ctor_get(v_opt_3045_, 1);
    v_map_3048_ = crate::leanh::lean_ctor_get(v_opts_3044_, 0);
    v___x_3049_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3048_,
            v_name_3046_,
        );
    if crate::leanh::lean_obj_tag(v___x_3049_) == 0 {
        let mut v___x_3050_: u8 = 0;
        v___x_3050_ = (crate::leanh::lean_unbox(v_defValue_3047_) as u8);
        return v___x_3050_;
    } else {
        let mut v_val_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3051_ = crate::leanh::lean_ctor_get(v___x_3049_, 0);
        crate::leanh::lean_inc(v_val_3051_);
        crate::leanh::lean_dec_ref_known(v___x_3049_, 1);
        if crate::leanh::lean_obj_tag(v_val_3051_) == 1 {
            let mut v_v_3052_: u8 = 0;
            v_v_3052_ = crate::leanh::lean_ctor_get_uint8(v_val_3051_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3051_, 0);
            return v_v_3052_;
        } else {
            let mut v___x_3053_: u8 = 0;
            crate::leanh::lean_dec(v_val_3051_);
            v___x_3053_ = (crate::leanh::lean_unbox(v_defValue_3047_) as u8);
            return v___x_3053_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1___boxed(
    mut v_opts_3054_: *mut crate::leanh::LeanObject,
    mut v_opt_3055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ =
        l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(v_opts_3054_, v_opt_3055_);
    crate::leanh::lean_dec_ref(v_opt_3055_);
    crate::leanh::lean_dec_ref(v_opts_3054_);
    v_r_3057_ = crate::leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3058_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_SymM_run_spec__0(
        crate::leanh::lean_box(0),
    );
    return v___x_3058_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3059_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3059_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__1,
    );
    v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3060_);
    return v___x_3061_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ = crate::leanh::lean_box(0);
    v___x_3063_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3064_ = lean_mk_array(v___x_3063_, v___x_3062_);
    return v___x_3064_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3065_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__3_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__3,
    );
    v___x_3066_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3067_, 0, v___x_3066_);
    crate::leanh::lean_ctor_set(v___x_3067_, 1, v___x_3065_);
    return v___x_3067_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once),
        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4,
    );
    v___x_3069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3068_);
    crate::leanh::lean_ctor_set(v___x_3069_, 1, v___x_3068_);
    return v___x_3069_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run___redArg(
    mut v_x_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_a_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u8 = 0;
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3104_: u8 = 0;
    let mut v_a_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v_ref_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_isSharedCheck_3120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                v___x_3077_ =
                    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_mkSharedExprs(v___x_3076_);
                v_fst_3078_ = crate::leanh::lean_ctor_get(v___x_3077_, 0);
                v_snd_3079_ = crate::leanh::lean_ctor_get(v___x_3077_, 1);
                v_isSharedCheck_3120_ = (!crate::leanh::lean_is_exclusive(v___x_3077_)) as u8;
                if v_isSharedCheck_3120_ == 0 {
                    v___x_3081_ = v___x_3077_;
                    v_isShared_3082_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3079_);
                    crate::leanh::lean_inc(v_fst_3078_);
                    crate::leanh::lean_dec(v___x_3077_);
                    v___x_3081_ = crate::leanh::lean_box(0);
                    v_isShared_3082_ = v_isSharedCheck_3120_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3083_ = l_Lean_Meta_Sym_SymExtensions_mkInitialStates();
                if crate::leanh::lean_obj_tag(v___x_3083_) == 0 {
                    crate::leanh::lean_del_object(v___x_3081_);
                    v_a_3084_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                    crate::leanh::lean_inc(v_a_3084_);
                    crate::leanh::lean_dec_ref_known(v___x_3083_, 1);
                    v_options_3085_ = crate::leanh::lean_ctor_get(v_a_3073_, 2);
                    v___x_3086_ = l_Lean_Meta_Sym_sym_debug;
                    v___x_3087_ = l_Lean_Option_get___at___00Lean_Meta_Sym_SymM_run_spec__1(
                        v_options_3085_,
                        v___x_3086_,
                    );
                    v___x_3088_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__2_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__2,
                    );
                    v___x_3089_ = crate::leanh::lean_box(0);
                    v___x_3090_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__5_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__5,
                    );
                    v___x_3091_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3091_, 0, v_snd_3079_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 1, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 2, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 3, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 4, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 5, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 6, v___x_3088_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 7, v_a_3084_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 8, v___x_3089_);
                    crate::leanh::lean_ctor_set(v___x_3091_, 9, v___x_3090_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3091_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v___x_3087_,
                    );
                    v___x_3092_ = lean_st_mk_ref(v___x_3091_);
                    v___x_3093_ = 1;
                    v___x_3094_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3094_, 0, v_fst_3078_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3094_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_3093_,
                    );
                    crate::leanh::lean_inc(v_a_3074_);
                    crate::leanh::lean_inc_ref(v_a_3073_);
                    crate::leanh::lean_inc(v_a_3072_);
                    crate::leanh::lean_inc_ref(v_a_3071_);
                    crate::leanh::lean_inc(v___x_3092_);
                    v___x_3095_ = crate::leanh::lean_apply_7(
                        v_x_3070_,
                        v___x_3094_,
                        v___x_3092_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3095_) == 0 {
                        v_a_3096_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                        v_isSharedCheck_3104_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3095_)) as u8;
                        if v_isSharedCheck_3104_ == 0 {
                            v___x_3098_ = v___x_3095_;
                            v_isShared_3099_ = v_isSharedCheck_3104_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3096_);
                            crate::leanh::lean_dec(v___x_3095_);
                            v___x_3098_ = crate::leanh::lean_box(0);
                            v_isShared_3099_ = v_isSharedCheck_3104_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3092_);
                        return v___x_3095_;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3079_);
                    crate::leanh::lean_dec(v_fst_3078_);
                    crate::leanh::lean_dec_ref(v_x_3070_);
                    v_a_3105_ = crate::leanh::lean_ctor_get(v___x_3083_, 0);
                    v_isSharedCheck_3119_ = (!crate::leanh::lean_is_exclusive(v___x_3083_)) as u8;
                    if v_isSharedCheck_3119_ == 0 {
                        v___x_3107_ = v___x_3083_;
                        v_isShared_3108_ = v_isSharedCheck_3119_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3105_);
                        crate::leanh::lean_dec(v___x_3083_);
                        v___x_3107_ = crate::leanh::lean_box(0);
                        v_isShared_3108_ = v_isSharedCheck_3119_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3100_ = lean_st_ref_get(v___x_3092_);
                crate::leanh::lean_dec(v___x_3092_);
                crate::leanh::lean_dec(v___x_3100_);
                if v_isShared_3099_ == 0 {
                    v___x_3102_ = v___x_3098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3096_);
                    v___x_3102_ = v_reuseFailAlloc_3103_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3102_;
            }
            4 => {
                v_ref_3109_ = crate::leanh::lean_ctor_get(v_a_3073_, 5);
                v___x_3110_ = lean_io_error_to_string(v_a_3105_);
                v___x_3111_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3111_, 0, v___x_3110_);
                v___x_3112_ = l_Lean_MessageData_ofFormat(v___x_3111_);
                crate::leanh::lean_inc(v_ref_3109_);
                if v_isShared_3082_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3081_, 1, v___x_3112_);
                    crate::leanh::lean_ctor_set(v___x_3081_, 0, v_ref_3109_);
                    v___x_3114_ = v___x_3081_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_ref_3109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3118_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3108_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3107_, 0, v___x_3114_);
                    v___x_3116_ = v___x_3107_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
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
    mut v_x_3121_: *mut crate::leanh::LeanObject,
    mut v_a_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3127_ =
        l_Lean_Meta_Sym_SymM_run___redArg(v_x_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_);
    crate::leanh::lean_dec(v_a_3125_);
    crate::leanh::lean_dec_ref(v_a_3124_);
    crate::leanh::lean_dec(v_a_3123_);
    crate::leanh::lean_dec_ref(v_a_3122_);
    return v_res_3127_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run(
    mut v_00_u03b1_3128_: *mut crate::leanh::LeanObject,
    mut v_x_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
    mut v_a_3133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3135_ =
        l_Lean_Meta_Sym_SymM_run___redArg(v_x_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
    return v___x_3135_;
}
pub unsafe fn l_Lean_Meta_Sym_SymM_run___boxed(
    mut v_00_u03b1_3136_: *mut crate::leanh::LeanObject,
    mut v_x_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Lean_Meta_Sym_SymM_run(
        v_00_u03b1_3136_,
        v_x_3137_,
        v_a_3138_,
        v_a_3139_,
        v_a_3140_,
        v_a_3141_,
    );
    crate::leanh::lean_dec(v_a_3141_);
    crate::leanh::lean_dec_ref(v_a_3140_);
    crate::leanh::lean_dec(v_a_3139_);
    crate::leanh::lean_dec_ref(v_a_3138_);
    return v_res_3143_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___redArg(
    mut v_a_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sharedExprs_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sharedExprs_3146_ = crate::leanh::lean_ctor_get(v_a_3144_, 0);
    crate::leanh::lean_inc_ref(v_sharedExprs_3146_);
    v___x_3147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3147_, 0, v_sharedExprs_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___redArg___boxed(
    mut v_a_3148_: *mut crate::leanh::LeanObject,
    mut v_a_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3150_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3148_);
    crate::leanh::lean_dec_ref(v_a_3148_);
    return v_res_3150_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs(
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
    mut v_a_3155_: *mut crate::leanh::LeanObject,
    mut v_a_3156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3158_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3151_);
    return v___x_3158_;
}
pub unsafe fn l_Lean_Meta_Sym_getSharedExprs___boxed(
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Lean_Meta_Sym_getSharedExprs(
        v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_,
    );
    crate::leanh::lean_dec(v_a_3164_);
    crate::leanh::lean_dec_ref(v_a_3163_);
    crate::leanh::lean_dec(v_a_3162_);
    crate::leanh::lean_dec_ref(v_a_3161_);
    crate::leanh::lean_dec(v_a_3160_);
    crate::leanh::lean_dec_ref(v_a_3159_);
    return v_res_3166_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr___redArg(
    mut v_a_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v_trueExpr_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3169_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3167_);
                v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                v_isSharedCheck_3178_ = (!crate::leanh::lean_is_exclusive(v___x_3169_)) as u8;
                if v_isSharedCheck_3178_ == 0 {
                    v___x_3172_ = v___x_3169_;
                    v_isShared_3173_ = v_isSharedCheck_3178_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3170_);
                    crate::leanh::lean_dec(v___x_3169_);
                    v___x_3172_ = crate::leanh::lean_box(0);
                    v_isShared_3173_ = v_isSharedCheck_3178_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trueExpr_3174_ = crate::leanh::lean_ctor_get(v_a_3170_, 0);
                crate::leanh::lean_inc_ref(v_trueExpr_3174_);
                crate::leanh::lean_dec(v_a_3170_);
                if v_isShared_3173_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3172_, 0, v_trueExpr_3174_);
                    v___x_3176_ = v___x_3172_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_trueExpr_3174_);
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
    mut v_a_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3181_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3179_);
    crate::leanh::lean_dec_ref(v_a_3179_);
    return v_res_3181_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr(
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
    mut v_a_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3182_);
    return v___x_3189_;
}
pub unsafe fn l_Lean_Meta_Sym_getTrueExpr___boxed(
    mut v_a_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_a_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3197_ = l_Lean_Meta_Sym_getTrueExpr(
        v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_,
    );
    crate::leanh::lean_dec(v_a_3195_);
    crate::leanh::lean_dec_ref(v_a_3194_);
    crate::leanh::lean_dec(v_a_3193_);
    crate::leanh::lean_dec_ref(v_a_3192_);
    crate::leanh::lean_dec(v_a_3191_);
    crate::leanh::lean_dec_ref(v_a_3190_);
    return v_res_3197_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr___redArg(
    mut v_e_3198_: *mut crate::leanh::LeanObject,
    mut v_a_3199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v_a_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3201_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3199_);
                if crate::leanh::lean_obj_tag(v___x_3201_) == 0 {
                    v_a_3202_ = crate::leanh::lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3211_ = (!crate::leanh::lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3211_ == 0 {
                        v___x_3204_ = v___x_3201_;
                        v_isShared_3205_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3202_);
                        crate::leanh::lean_dec(v___x_3201_);
                        v___x_3204_ = crate::leanh::lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3211_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3212_ = crate::leanh::lean_ctor_get(v___x_3201_, 0);
                    v_isSharedCheck_3219_ = (!crate::leanh::lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3219_ == 0 {
                        v___x_3214_ = v___x_3201_;
                        v_isShared_3215_ = v_isSharedCheck_3219_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3212_);
                        crate::leanh::lean_dec(v___x_3201_);
                        v___x_3214_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_a_3202_);
                v___x_3207_ = crate::leanh::lean_box((v___x_3206_) as usize);
                if v_isShared_3205_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3204_, 0, v___x_3207_);
                    v___x_3209_ = v___x_3204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3207_);
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
                    v_reuseFailAlloc_3218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
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
    mut v_e_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_3220_, v_a_3221_);
    crate::leanh::lean_dec_ref(v_a_3221_);
    crate::leanh::lean_dec_ref(v_e_3220_);
    return v_res_3223_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr(
    mut v_e_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
    mut v_a_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3232_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_3224_, v_a_3225_);
    return v___x_3232_;
}
pub unsafe fn l_Lean_Meta_Sym_isTrueExpr___boxed(
    mut v_e_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
    mut v_a_3240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3241_ = l_Lean_Meta_Sym_isTrueExpr(
        v_e_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_,
    );
    crate::leanh::lean_dec(v_a_3239_);
    crate::leanh::lean_dec_ref(v_a_3238_);
    crate::leanh::lean_dec(v_a_3237_);
    crate::leanh::lean_dec_ref(v_a_3236_);
    crate::leanh::lean_dec(v_a_3235_);
    crate::leanh::lean_dec_ref(v_a_3234_);
    crate::leanh::lean_dec_ref(v_e_3233_);
    return v_res_3241_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr___redArg(
    mut v_a_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v_falseExpr_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3244_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3242_);
                v_a_3245_ = crate::leanh::lean_ctor_get(v___x_3244_, 0);
                v_isSharedCheck_3253_ = (!crate::leanh::lean_is_exclusive(v___x_3244_)) as u8;
                if v_isSharedCheck_3253_ == 0 {
                    v___x_3247_ = v___x_3244_;
                    v_isShared_3248_ = v_isSharedCheck_3253_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3245_);
                    crate::leanh::lean_dec(v___x_3244_);
                    v___x_3247_ = crate::leanh::lean_box(0);
                    v_isShared_3248_ = v_isSharedCheck_3253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_falseExpr_3249_ = crate::leanh::lean_ctor_get(v_a_3245_, 1);
                crate::leanh::lean_inc_ref(v_falseExpr_3249_);
                crate::leanh::lean_dec(v_a_3245_);
                if v_isShared_3248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3247_, 0, v_falseExpr_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_falseExpr_3249_);
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
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_a_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3254_);
    crate::leanh::lean_dec_ref(v_a_3254_);
    return v_res_3256_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr(
    mut v_a_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3264_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3257_);
    return v___x_3264_;
}
pub unsafe fn l_Lean_Meta_Sym_getFalseExpr___boxed(
    mut v_a_3265_: *mut crate::leanh::LeanObject,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
    mut v_a_3267_: *mut crate::leanh::LeanObject,
    mut v_a_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3272_ = l_Lean_Meta_Sym_getFalseExpr(
        v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_,
    );
    crate::leanh::lean_dec(v_a_3270_);
    crate::leanh::lean_dec_ref(v_a_3269_);
    crate::leanh::lean_dec(v_a_3268_);
    crate::leanh::lean_dec_ref(v_a_3267_);
    crate::leanh::lean_dec(v_a_3266_);
    crate::leanh::lean_dec_ref(v_a_3265_);
    return v_res_3272_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr___redArg(
    mut v_e_3273_: *mut crate::leanh::LeanObject,
    mut v_a_3274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3281_: u8 = 0;
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_a_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3290_: u8 = 0;
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3276_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_3274_);
                if crate::leanh::lean_obj_tag(v___x_3276_) == 0 {
                    v_a_3277_ = crate::leanh::lean_ctor_get(v___x_3276_, 0);
                    v_isSharedCheck_3286_ = (!crate::leanh::lean_is_exclusive(v___x_3276_)) as u8;
                    if v_isSharedCheck_3286_ == 0 {
                        v___x_3279_ = v___x_3276_;
                        v_isShared_3280_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3277_);
                        crate::leanh::lean_dec(v___x_3276_);
                        v___x_3279_ = crate::leanh::lean_box(0);
                        v_isShared_3280_ = v_isSharedCheck_3286_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3287_ = crate::leanh::lean_ctor_get(v___x_3276_, 0);
                    v_isSharedCheck_3294_ = (!crate::leanh::lean_is_exclusive(v___x_3276_)) as u8;
                    if v_isSharedCheck_3294_ == 0 {
                        v___x_3289_ = v___x_3276_;
                        v_isShared_3290_ = v_isSharedCheck_3294_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3287_);
                        crate::leanh::lean_dec(v___x_3276_);
                        v___x_3289_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_a_3277_);
                v___x_3282_ = crate::leanh::lean_box((v___x_3281_) as usize);
                if v_isShared_3280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3282_);
                    v___x_3284_ = v___x_3279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
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
                    v_reuseFailAlloc_3293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
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
    mut v_e_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_3295_, v_a_3296_);
    crate::leanh::lean_dec_ref(v_a_3296_);
    crate::leanh::lean_dec_ref(v_e_3295_);
    return v_res_3298_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr(
    mut v_e_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_3299_, v_a_3300_);
    return v___x_3307_;
}
pub unsafe fn l_Lean_Meta_Sym_isFalseExpr___boxed(
    mut v_e_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3316_ = l_Lean_Meta_Sym_isFalseExpr(
        v_e_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_,
    );
    crate::leanh::lean_dec(v_a_3314_);
    crate::leanh::lean_dec_ref(v_a_3313_);
    crate::leanh::lean_dec(v_a_3312_);
    crate::leanh::lean_dec_ref(v_a_3311_);
    crate::leanh::lean_dec(v_a_3310_);
    crate::leanh::lean_dec_ref(v_a_3309_);
    crate::leanh::lean_dec_ref(v_e_3308_);
    return v_res_3316_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr___redArg(
    mut v_a_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v_btrueExpr_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3319_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3317_);
                v_a_3320_ = crate::leanh::lean_ctor_get(v___x_3319_, 0);
                v_isSharedCheck_3328_ = (!crate::leanh::lean_is_exclusive(v___x_3319_)) as u8;
                if v_isSharedCheck_3328_ == 0 {
                    v___x_3322_ = v___x_3319_;
                    v_isShared_3323_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3320_);
                    crate::leanh::lean_dec(v___x_3319_);
                    v___x_3322_ = crate::leanh::lean_box(0);
                    v_isShared_3323_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_btrueExpr_3324_ = crate::leanh::lean_ctor_get(v_a_3320_, 3);
                crate::leanh::lean_inc_ref(v_btrueExpr_3324_);
                crate::leanh::lean_dec(v_a_3320_);
                if v_isShared_3323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3322_, 0, v_btrueExpr_3324_);
                    v___x_3326_ = v___x_3322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_btrueExpr_3324_);
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
    mut v_a_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3329_);
    crate::leanh::lean_dec_ref(v_a_3329_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr(
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3332_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolTrueExpr___boxed(
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3347_ = l_Lean_Meta_Sym_getBoolTrueExpr(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_,
    );
    crate::leanh::lean_dec(v_a_3345_);
    crate::leanh::lean_dec_ref(v_a_3344_);
    crate::leanh::lean_dec(v_a_3343_);
    crate::leanh::lean_dec_ref(v_a_3342_);
    crate::leanh::lean_dec(v_a_3341_);
    crate::leanh::lean_dec_ref(v_a_3340_);
    return v_res_3347_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr___redArg(
    mut v_e_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3355_: u8 = 0;
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3361_: u8 = 0;
    let mut v_a_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3365_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3351_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3349_);
                if crate::leanh::lean_obj_tag(v___x_3351_) == 0 {
                    v_a_3352_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                    v_isSharedCheck_3361_ = (!crate::leanh::lean_is_exclusive(v___x_3351_)) as u8;
                    if v_isSharedCheck_3361_ == 0 {
                        v___x_3354_ = v___x_3351_;
                        v_isShared_3355_ = v_isSharedCheck_3361_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3352_);
                        crate::leanh::lean_dec(v___x_3351_);
                        v___x_3354_ = crate::leanh::lean_box(0);
                        v_isShared_3355_ = v_isSharedCheck_3361_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3362_ = crate::leanh::lean_ctor_get(v___x_3351_, 0);
                    v_isSharedCheck_3369_ = (!crate::leanh::lean_is_exclusive(v___x_3351_)) as u8;
                    if v_isSharedCheck_3369_ == 0 {
                        v___x_3364_ = v___x_3351_;
                        v_isShared_3365_ = v_isSharedCheck_3369_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3362_);
                        crate::leanh::lean_dec(v___x_3351_);
                        v___x_3364_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_a_3352_);
                v___x_3357_ = crate::leanh::lean_box((v___x_3356_) as usize);
                if v_isShared_3355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3354_, 0, v___x_3357_);
                    v___x_3359_ = v___x_3354_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
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
                    v_reuseFailAlloc_3368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
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
    mut v_e_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
    mut v_a_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_3370_, v_a_3371_);
    crate::leanh::lean_dec_ref(v_a_3371_);
    crate::leanh::lean_dec_ref(v_e_3370_);
    return v_res_3373_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr(
    mut v_e_3374_: *mut crate::leanh::LeanObject,
    mut v_a_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
    mut v_a_3378_: *mut crate::leanh::LeanObject,
    mut v_a_3379_: *mut crate::leanh::LeanObject,
    mut v_a_3380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3382_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_3374_, v_a_3375_);
    return v___x_3382_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolTrueExpr___boxed(
    mut v_e_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_a_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l_Lean_Meta_Sym_isBoolTrueExpr(
        v_e_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_,
    );
    crate::leanh::lean_dec(v_a_3389_);
    crate::leanh::lean_dec_ref(v_a_3388_);
    crate::leanh::lean_dec(v_a_3387_);
    crate::leanh::lean_dec_ref(v_a_3386_);
    crate::leanh::lean_dec(v_a_3385_);
    crate::leanh::lean_dec_ref(v_a_3384_);
    crate::leanh::lean_dec_ref(v_e_3383_);
    return v_res_3391_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr___redArg(
    mut v_a_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v_bfalseExpr_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3394_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3392_);
                v_a_3395_ = crate::leanh::lean_ctor_get(v___x_3394_, 0);
                v_isSharedCheck_3403_ = (!crate::leanh::lean_is_exclusive(v___x_3394_)) as u8;
                if v_isSharedCheck_3403_ == 0 {
                    v___x_3397_ = v___x_3394_;
                    v_isShared_3398_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3395_);
                    crate::leanh::lean_dec(v___x_3394_);
                    v___x_3397_ = crate::leanh::lean_box(0);
                    v_isShared_3398_ = v_isSharedCheck_3403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_bfalseExpr_3399_ = crate::leanh::lean_ctor_get(v_a_3395_, 4);
                crate::leanh::lean_inc_ref(v_bfalseExpr_3399_);
                crate::leanh::lean_dec(v_a_3395_);
                if v_isShared_3398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3397_, 0, v_bfalseExpr_3399_);
                    v___x_3401_ = v___x_3397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3402_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_bfalseExpr_3399_);
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
    mut v_a_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3406_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3404_);
    crate::leanh::lean_dec_ref(v_a_3404_);
    return v_res_3406_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr(
    mut v_a_3407_: *mut crate::leanh::LeanObject,
    mut v_a_3408_: *mut crate::leanh::LeanObject,
    mut v_a_3409_: *mut crate::leanh::LeanObject,
    mut v_a_3410_: *mut crate::leanh::LeanObject,
    mut v_a_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3407_);
    return v___x_3414_;
}
pub unsafe fn l_Lean_Meta_Sym_getBoolFalseExpr___boxed(
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3422_ = l_Lean_Meta_Sym_getBoolFalseExpr(
        v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_,
    );
    crate::leanh::lean_dec(v_a_3420_);
    crate::leanh::lean_dec_ref(v_a_3419_);
    crate::leanh::lean_dec(v_a_3418_);
    crate::leanh::lean_dec_ref(v_a_3417_);
    crate::leanh::lean_dec(v_a_3416_);
    crate::leanh::lean_dec_ref(v_a_3415_);
    return v_res_3422_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr___redArg(
    mut v_e_3423_: *mut crate::leanh::LeanObject,
    mut v_a_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3430_: u8 = 0;
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3444_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3426_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3424_);
                if crate::leanh::lean_obj_tag(v___x_3426_) == 0 {
                    v_a_3427_ = crate::leanh::lean_ctor_get(v___x_3426_, 0);
                    v_isSharedCheck_3436_ = (!crate::leanh::lean_is_exclusive(v___x_3426_)) as u8;
                    if v_isSharedCheck_3436_ == 0 {
                        v___x_3429_ = v___x_3426_;
                        v_isShared_3430_ = v_isSharedCheck_3436_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3427_);
                        crate::leanh::lean_dec(v___x_3426_);
                        v___x_3429_ = crate::leanh::lean_box(0);
                        v_isShared_3430_ = v_isSharedCheck_3436_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3426_, 0);
                    v_isSharedCheck_3444_ = (!crate::leanh::lean_is_exclusive(v___x_3426_)) as u8;
                    if v_isSharedCheck_3444_ == 0 {
                        v___x_3439_ = v___x_3426_;
                        v_isShared_3440_ = v_isSharedCheck_3444_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3437_);
                        crate::leanh::lean_dec(v___x_3426_);
                        v___x_3439_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_a_3427_);
                v___x_3432_ = crate::leanh::lean_box((v___x_3431_) as usize);
                if v_isShared_3430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3429_, 0, v___x_3432_);
                    v___x_3434_ = v___x_3429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
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
                    v_reuseFailAlloc_3443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
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
    mut v_e_3445_: *mut crate::leanh::LeanObject,
    mut v_a_3446_: *mut crate::leanh::LeanObject,
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_3445_, v_a_3446_);
    crate::leanh::lean_dec_ref(v_a_3446_);
    crate::leanh::lean_dec_ref(v_e_3445_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr(
    mut v_e_3449_: *mut crate::leanh::LeanObject,
    mut v_a_3450_: *mut crate::leanh::LeanObject,
    mut v_a_3451_: *mut crate::leanh::LeanObject,
    mut v_a_3452_: *mut crate::leanh::LeanObject,
    mut v_a_3453_: *mut crate::leanh::LeanObject,
    mut v_a_3454_: *mut crate::leanh::LeanObject,
    mut v_a_3455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3457_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_3449_, v_a_3450_);
    return v___x_3457_;
}
pub unsafe fn l_Lean_Meta_Sym_isBoolFalseExpr___boxed(
    mut v_e_3458_: *mut crate::leanh::LeanObject,
    mut v_a_3459_: *mut crate::leanh::LeanObject,
    mut v_a_3460_: *mut crate::leanh::LeanObject,
    mut v_a_3461_: *mut crate::leanh::LeanObject,
    mut v_a_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
    mut v_a_3464_: *mut crate::leanh::LeanObject,
    mut v_a_3465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3466_ = l_Lean_Meta_Sym_isBoolFalseExpr(
        v_e_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_,
    );
    crate::leanh::lean_dec(v_a_3464_);
    crate::leanh::lean_dec_ref(v_a_3463_);
    crate::leanh::lean_dec(v_a_3462_);
    crate::leanh::lean_dec_ref(v_a_3461_);
    crate::leanh::lean_dec(v_a_3460_);
    crate::leanh::lean_dec_ref(v_a_3459_);
    crate::leanh::lean_dec_ref(v_e_3458_);
    return v_res_3466_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr___redArg(
    mut v_a_3467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v_natZExpr_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3469_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3467_);
                v_a_3470_ = crate::leanh::lean_ctor_get(v___x_3469_, 0);
                v_isSharedCheck_3478_ = (!crate::leanh::lean_is_exclusive(v___x_3469_)) as u8;
                if v_isSharedCheck_3478_ == 0 {
                    v___x_3472_ = v___x_3469_;
                    v_isShared_3473_ = v_isSharedCheck_3478_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3470_);
                    crate::leanh::lean_dec(v___x_3469_);
                    v___x_3472_ = crate::leanh::lean_box(0);
                    v_isShared_3473_ = v_isSharedCheck_3478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_natZExpr_3474_ = crate::leanh::lean_ctor_get(v_a_3470_, 2);
                crate::leanh::lean_inc_ref(v_natZExpr_3474_);
                crate::leanh::lean_dec(v_a_3470_);
                if v_isShared_3473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3472_, 0, v_natZExpr_3474_);
                    v___x_3476_ = v___x_3472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_natZExpr_3474_);
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
    mut v_a_3479_: *mut crate::leanh::LeanObject,
    mut v_a_3480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_3479_);
    crate::leanh::lean_dec_ref(v_a_3479_);
    return v_res_3481_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr(
    mut v_a_3482_: *mut crate::leanh::LeanObject,
    mut v_a_3483_: *mut crate::leanh::LeanObject,
    mut v_a_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = l_Lean_Meta_Sym_getNatZeroExpr___redArg(v_a_3482_);
    return v___x_3489_;
}
pub unsafe fn l_Lean_Meta_Sym_getNatZeroExpr___boxed(
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3497_ = l_Lean_Meta_Sym_getNatZeroExpr(
        v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_,
    );
    crate::leanh::lean_dec(v_a_3495_);
    crate::leanh::lean_dec_ref(v_a_3494_);
    crate::leanh::lean_dec(v_a_3493_);
    crate::leanh::lean_dec_ref(v_a_3492_);
    crate::leanh::lean_dec(v_a_3491_);
    crate::leanh::lean_dec_ref(v_a_3490_);
    return v_res_3497_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr___redArg(
    mut v_a_3498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v_ordEqExpr_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3500_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3498_);
                v_a_3501_ = crate::leanh::lean_ctor_get(v___x_3500_, 0);
                v_isSharedCheck_3509_ = (!crate::leanh::lean_is_exclusive(v___x_3500_)) as u8;
                if v_isSharedCheck_3509_ == 0 {
                    v___x_3503_ = v___x_3500_;
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3501_);
                    crate::leanh::lean_dec(v___x_3500_);
                    v___x_3503_ = crate::leanh::lean_box(0);
                    v_isShared_3504_ = v_isSharedCheck_3509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ordEqExpr_3505_ = crate::leanh::lean_ctor_get(v_a_3501_, 5);
                crate::leanh::lean_inc_ref(v_ordEqExpr_3505_);
                crate::leanh::lean_dec(v_a_3501_);
                if v_isShared_3504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3503_, 0, v_ordEqExpr_3505_);
                    v___x_3507_ = v___x_3503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_ordEqExpr_3505_);
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
    mut v_a_3510_: *mut crate::leanh::LeanObject,
    mut v_a_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_3510_);
    crate::leanh::lean_dec_ref(v_a_3510_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr(
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_3513_);
    return v___x_3520_;
}
pub unsafe fn l_Lean_Meta_Sym_getOrderingEqExpr___boxed(
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3528_ = l_Lean_Meta_Sym_getOrderingEqExpr(
        v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_,
    );
    crate::leanh::lean_dec(v_a_3526_);
    crate::leanh::lean_dec_ref(v_a_3525_);
    crate::leanh::lean_dec(v_a_3524_);
    crate::leanh::lean_dec_ref(v_a_3523_);
    crate::leanh::lean_dec(v_a_3522_);
    crate::leanh::lean_dec_ref(v_a_3521_);
    return v_res_3528_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr___redArg(
    mut v_a_3529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v_intExpr_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3531_ = l_Lean_Meta_Sym_getSharedExprs___redArg(v_a_3529_);
                v_a_3532_ = crate::leanh::lean_ctor_get(v___x_3531_, 0);
                v_isSharedCheck_3540_ = (!crate::leanh::lean_is_exclusive(v___x_3531_)) as u8;
                if v_isSharedCheck_3540_ == 0 {
                    v___x_3534_ = v___x_3531_;
                    v_isShared_3535_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3532_);
                    crate::leanh::lean_dec(v___x_3531_);
                    v___x_3534_ = crate::leanh::lean_box(0);
                    v_isShared_3535_ = v_isSharedCheck_3540_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_intExpr_3536_ = crate::leanh::lean_ctor_get(v_a_3532_, 6);
                crate::leanh::lean_inc_ref(v_intExpr_3536_);
                crate::leanh::lean_dec(v_a_3532_);
                if v_isShared_3535_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3534_, 0, v_intExpr_3536_);
                    v___x_3538_ = v___x_3534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_intExpr_3536_);
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
    mut v_a_3541_: *mut crate::leanh::LeanObject,
    mut v_a_3542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3543_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_3541_);
    crate::leanh::lean_dec_ref(v_a_3541_);
    return v_res_3543_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr(
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Meta_Sym_getIntExpr___redArg(v_a_3544_);
    return v___x_3551_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntExpr___boxed(
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_Meta_Sym_getIntExpr(
        v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_,
    );
    crate::leanh::lean_dec(v_a_3557_);
    crate::leanh::lean_dec_ref(v_a_3556_);
    crate::leanh::lean_dec(v_a_3555_);
    crate::leanh::lean_dec_ref(v_a_3554_);
    crate::leanh::lean_dec(v_a_3553_);
    crate::leanh::lean_dec_ref(v_a_3552_);
    return v_res_3559_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3560_: *mut crate::leanh::LeanObject,
    mut v_vals_3561_: *mut crate::leanh::LeanObject,
    mut v_i_3562_: *mut crate::leanh::LeanObject,
    mut v_k_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_array_get_size(v_keys_3560_);
                v___x_3565_ = lean_nat_dec_lt(v_i_3562_, v___x_3564_);
                if v___x_3565_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_3563_);
                    crate::leanh::lean_dec(v_i_3562_);
                    v___x_3566_ = crate::leanh::lean_box(0);
                    return v___x_3566_;
                } else {
                    v_k_x27_3567_ = lean_array_fget_borrowed(v_keys_3560_, v_i_3562_);
                    crate::leanh::lean_inc(v_k_x27_3567_);
                    crate::leanh::lean_inc_ref(v_k_3563_);
                    v___x_3568_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_3563_,
                            v_k_x27_3567_,
                        );
                    if v___x_3568_ == 0 {
                        v___x_3569_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3570_ = lean_nat_add(v_i_3562_, v___x_3569_);
                        crate::leanh::lean_dec(v_i_3562_);
                        v_i_3562_ = v___x_3570_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_3563_);
                        v___x_3572_ = lean_array_fget_borrowed(v_vals_3561_, v_i_3562_);
                        crate::leanh::lean_dec(v_i_3562_);
                        crate::leanh::lean_inc(v___x_3572_);
                        crate::leanh::lean_inc(v_k_x27_3567_);
                        v___x_3573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3573_, 0, v_k_x27_3567_);
                        crate::leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                        v___x_3574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3573_);
                        return v___x_3574_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3575_: *mut crate::leanh::LeanObject,
    mut v_vals_3576_: *mut crate::leanh::LeanObject,
    mut v_i_3577_: *mut crate::leanh::LeanObject,
    mut v_k_3578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3579_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_3575_, v_vals_3576_, v_i_3577_, v_k_3578_);
    crate::leanh::lean_dec_ref(v_vals_3576_);
    crate::leanh::lean_dec_ref(v_keys_3575_);
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
    v___x_3584_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__0);
    v___x_3585_ = lean_usize_sub(v___x_3584_, v___x_3583_);
    return v___x_3585_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(
    mut v_x_3586_: *mut crate::leanh::LeanObject,
    mut v_x_3587_: usize,
    mut v_x_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: usize = 0;
    let mut v_j_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: usize = 0;
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3586_) == 0 {
                    v_es_3589_ = crate::leanh::lean_ctor_get(v_x_3586_, 0);
                    crate::leanh::lean_inc_ref(v_es_3589_);
                    crate::leanh::lean_dec_ref_known(v_x_3586_, 1);
                    v___x_3590_ = crate::leanh::lean_box(2);
                    v___x_3591_ = 5usize;
                    v___x_3592_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_3593_ = lean_usize_land(v_x_3587_, v___x_3592_);
                    v_j_3594_ = lean_usize_to_nat(v___x_3593_);
                    v___x_3595_ = lean_array_get(v___x_3590_, v_es_3589_, v_j_3594_);
                    crate::leanh::lean_dec(v_j_3594_);
                    crate::leanh::lean_dec_ref(v_es_3589_);
                    match crate::leanh::lean_obj_tag(v___x_3595_) {
                        0 => {
                            v_key_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                            crate::leanh::lean_inc_n(v_key_3596_, 2);
                            v_val_3597_ = crate::leanh::lean_ctor_get(v___x_3595_, 1);
                            crate::leanh::lean_inc(v_val_3597_);
                            crate::leanh::lean_dec_ref_known(v___x_3595_, 2);
                            v___x_3598_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_3588_,
                                    v_key_3596_,
                                );
                            if v___x_3598_ == 0 {
                                crate::leanh::lean_dec(v_val_3597_);
                                crate::leanh::lean_dec(v_key_3596_);
                                v___x_3599_ = crate::leanh::lean_box(0);
                                return v___x_3599_;
                            } else {
                                v___x_3600_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3600_, 0, v_key_3596_);
                                crate::leanh::lean_ctor_set(v___x_3600_, 1, v_val_3597_);
                                v___x_3601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3601_, 0, v___x_3600_);
                                return v___x_3601_;
                            }
                        }
                        1 => {
                            v_node_3602_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                            crate::leanh::lean_inc(v_node_3602_);
                            crate::leanh::lean_dec_ref_known(v___x_3595_, 1);
                            v___x_3603_ = lean_usize_shift_right(v_x_3587_, v___x_3591_);
                            v_x_3586_ = v_node_3602_;
                            v_x_3587_ = v___x_3603_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_3588_);
                            v___x_3605_ = crate::leanh::lean_box(0);
                            return v___x_3605_;
                        }
                    }
                } else {
                    v_ks_3606_ = crate::leanh::lean_ctor_get(v_x_3586_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3606_);
                    v_vs_3607_ = crate::leanh::lean_ctor_get(v_x_3586_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3607_);
                    crate::leanh::lean_dec_ref_known(v_x_3586_, 2);
                    v___x_3608_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3609_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_ks_3606_, v_vs_3607_, v___x_3608_, v_x_3588_);
                    crate::leanh::lean_dec_ref(v_vs_3607_);
                    crate::leanh::lean_dec_ref(v_ks_3606_);
                    return v___x_3609_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___boxed(
    mut v_x_3610_: *mut crate::leanh::LeanObject,
    mut v_x_3611_: *mut crate::leanh::LeanObject,
    mut v_x_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2093__boxed_3613_: usize = 0;
    let mut v_res_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2093__boxed_3613_ = crate::leanh::lean_unbox_usize(v_x_3611_);
    crate::leanh::lean_dec(v_x_3611_);
    v_res_3614_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3610_, v_x_2093__boxed_3613_, v_x_3612_);
    return v_res_3614_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
    mut v_x_3615_: *mut crate::leanh::LeanObject,
    mut v_x_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3617_: u64 = 0;
    let mut v___x_3618_: usize = 0;
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3617_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_3616_);
    v___x_3618_ = lean_uint64_to_usize(v___x_3617_);
    crate::leanh::lean_inc_ref(v_x_3615_);
    v___x_3619_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3615_, v___x_3618_, v_x_3616_);
    return v___x_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg___boxed(
    mut v_x_3620_: *mut crate::leanh::LeanObject,
    mut v_x_3621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3622_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
            v_x_3620_, v_x_3621_,
        );
    crate::leanh::lean_dec_ref(v_x_3620_);
    return v_res_3622_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___redArg(
    mut v_e_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3637_: u8 = 0;
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3658_: u8 = 0;
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v_unused_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3626_ = lean_st_ref_take(v_a_3624_);
                v_share_3627_ = crate::leanh::lean_ctor_get(v___x_3626_, 0);
                v_maxFVar_3628_ = crate::leanh::lean_ctor_get(v___x_3626_, 1);
                v_proofInstInfo_3629_ = crate::leanh::lean_ctor_get(v___x_3626_, 2);
                v_inferType_3630_ = crate::leanh::lean_ctor_get(v___x_3626_, 3);
                v_getLevel_3631_ = crate::leanh::lean_ctor_get(v___x_3626_, 4);
                v_congrInfo_3632_ = crate::leanh::lean_ctor_get(v___x_3626_, 5);
                v_defEqI_3633_ = crate::leanh::lean_ctor_get(v___x_3626_, 6);
                v_extensions_3634_ = crate::leanh::lean_ctor_get(v___x_3626_, 7);
                v_issues_3635_ = crate::leanh::lean_ctor_get(v___x_3626_, 8);
                v_canon_3636_ = crate::leanh::lean_ctor_get(v___x_3626_, 9);
                v_debug_3637_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3626_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3679_ = (!crate::leanh::lean_is_exclusive(v___x_3626_)) as u8;
                if v_isSharedCheck_3679_ == 0 {
                    v___x_3639_ = v___x_3626_;
                    v_isShared_3640_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3636_);
                    crate::leanh::lean_inc(v_issues_3635_);
                    crate::leanh::lean_inc(v_extensions_3634_);
                    crate::leanh::lean_inc(v_defEqI_3633_);
                    crate::leanh::lean_inc(v_congrInfo_3632_);
                    crate::leanh::lean_inc(v_getLevel_3631_);
                    crate::leanh::lean_inc(v_inferType_3630_);
                    crate::leanh::lean_inc(v_proofInstInfo_3629_);
                    crate::leanh::lean_inc(v_maxFVar_3628_);
                    crate::leanh::lean_inc(v_share_3627_);
                    crate::leanh::lean_dec(v___x_3626_);
                    v___x_3639_ = crate::leanh::lean_box(0);
                    v_isShared_3640_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3641_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                if v_isShared_3640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3639_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3678_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_maxFVar_3628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_proofInstInfo_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 3, v_inferType_3630_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 4, v_getLevel_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 5, v_congrInfo_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 6, v_defEqI_3633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 7, v_extensions_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 8, v_issues_3635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3678_, 9, v_canon_3636_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3678_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_3637_,
                    );
                    v___x_3643_ = v_reuseFailAlloc_3678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3644_ = lean_st_ref_set(v_a_3624_, v___x_3643_);
                crate::leanh::lean_inc_ref(v_e_3623_);
                v___x_3669_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(v_share_3627_, v_e_3623_);
                if crate::leanh::lean_obj_tag(v___x_3669_) == 0 {
                    v___x_3670_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__4_once),
                        _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__4,
                    );
                    v___x_3671_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3671_, 0, v___x_3670_);
                    crate::leanh::lean_ctor_set(v___x_3671_, 1, v_share_3627_);
                    v___x_3672_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_go(
                        v_e_3623_,
                        v___x_3671_,
                    );
                    v_snd_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 1);
                    crate::leanh::lean_inc(v_snd_3673_);
                    v_fst_3674_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                    crate::leanh::lean_inc(v_fst_3674_);
                    crate::leanh::lean_dec_ref(v___x_3672_);
                    v_set_3675_ = crate::leanh::lean_ctor_get(v_snd_3673_, 1);
                    crate::leanh::lean_inc_ref(v_set_3675_);
                    crate::leanh::lean_dec(v_snd_3673_);
                    v_fst_3646_ = v_fst_3674_;
                    v_snd_3647_ = v_set_3675_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3623_);
                    v_val_3676_ = crate::leanh::lean_ctor_get(v___x_3669_, 0);
                    crate::leanh::lean_inc(v_val_3676_);
                    crate::leanh::lean_dec_ref_known(v___x_3669_, 1);
                    v_fst_3677_ = crate::leanh::lean_ctor_get(v_val_3676_, 0);
                    crate::leanh::lean_inc(v_fst_3677_);
                    crate::leanh::lean_dec(v_val_3676_);
                    v_fst_3646_ = v_fst_3677_;
                    v_snd_3647_ = v_share_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3648_ = lean_st_ref_take(v_a_3624_);
                v_maxFVar_3649_ = crate::leanh::lean_ctor_get(v___x_3648_, 1);
                v_proofInstInfo_3650_ = crate::leanh::lean_ctor_get(v___x_3648_, 2);
                v_inferType_3651_ = crate::leanh::lean_ctor_get(v___x_3648_, 3);
                v_getLevel_3652_ = crate::leanh::lean_ctor_get(v___x_3648_, 4);
                v_congrInfo_3653_ = crate::leanh::lean_ctor_get(v___x_3648_, 5);
                v_defEqI_3654_ = crate::leanh::lean_ctor_get(v___x_3648_, 6);
                v_extensions_3655_ = crate::leanh::lean_ctor_get(v___x_3648_, 7);
                v_issues_3656_ = crate::leanh::lean_ctor_get(v___x_3648_, 8);
                v_canon_3657_ = crate::leanh::lean_ctor_get(v___x_3648_, 9);
                v_debug_3658_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3648_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3667_ = (!crate::leanh::lean_is_exclusive(v___x_3648_)) as u8;
                if v_isSharedCheck_3667_ == 0 {
                    v_unused_3668_ = crate::leanh::lean_ctor_get(v___x_3648_, 0);
                    crate::leanh::lean_dec(v_unused_3668_);
                    v___x_3660_ = v___x_3648_;
                    v_isShared_3661_ = v_isSharedCheck_3667_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3657_);
                    crate::leanh::lean_inc(v_issues_3656_);
                    crate::leanh::lean_inc(v_extensions_3655_);
                    crate::leanh::lean_inc(v_defEqI_3654_);
                    crate::leanh::lean_inc(v_congrInfo_3653_);
                    crate::leanh::lean_inc(v_getLevel_3652_);
                    crate::leanh::lean_inc(v_inferType_3651_);
                    crate::leanh::lean_inc(v_proofInstInfo_3650_);
                    crate::leanh::lean_inc(v_maxFVar_3649_);
                    crate::leanh::lean_dec(v___x_3648_);
                    v___x_3660_ = crate::leanh::lean_box(0);
                    v_isShared_3661_ = v_isSharedCheck_3667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3661_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3660_, 0, v_snd_3647_);
                    v___x_3663_ = v___x_3660_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_snd_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_maxFVar_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_proofInstInfo_3650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 3, v_inferType_3651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 4, v_getLevel_3652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 5, v_congrInfo_3653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 6, v_defEqI_3654_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 7, v_extensions_3655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 8, v_issues_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 9, v_canon_3657_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3666_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_3658_,
                    );
                    v___x_3663_ = v_reuseFailAlloc_3666_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3664_ = lean_st_ref_set(v_a_3624_, v___x_3663_);
                v___x_3665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3665_, 0, v_fst_3646_);
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___redArg___boxed(
    mut v_e_3680_: *mut crate::leanh::LeanObject,
    mut v_a_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3683_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_3680_, v_a_3681_);
    crate::leanh::lean_dec(v_a_3681_);
    return v_res_3683_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon(
    mut v_e_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
    mut v_a_3690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3692_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_3684_, v_a_3686_);
    return v___x_3692_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommon___boxed(
    mut v_e_3693_: *mut crate::leanh::LeanObject,
    mut v_a_3694_: *mut crate::leanh::LeanObject,
    mut v_a_3695_: *mut crate::leanh::LeanObject,
    mut v_a_3696_: *mut crate::leanh::LeanObject,
    mut v_a_3697_: *mut crate::leanh::LeanObject,
    mut v_a_3698_: *mut crate::leanh::LeanObject,
    mut v_a_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3701_ = l_Lean_Meta_Sym_shareCommon(
        v_e_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_,
    );
    crate::leanh::lean_dec(v_a_3699_);
    crate::leanh::lean_dec_ref(v_a_3698_);
    crate::leanh::lean_dec(v_a_3697_);
    crate::leanh::lean_dec_ref(v_a_3696_);
    crate::leanh::lean_dec(v_a_3695_);
    crate::leanh::lean_dec_ref(v_a_3694_);
    return v_res_3701_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(
    mut v_00_u03b2_3702_: *mut crate::leanh::LeanObject,
    mut v_x_3703_: *mut crate::leanh::LeanObject,
    mut v_x_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3705_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___redArg(
            v_x_3703_, v_x_3704_,
        );
    return v___x_3705_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0___boxed(
    mut v_00_u03b2_3706_: *mut crate::leanh::LeanObject,
    mut v_x_3707_: *mut crate::leanh::LeanObject,
    mut v_x_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0(
        v_00_u03b2_3706_,
        v_x_3707_,
        v_x_3708_,
    );
    crate::leanh::lean_dec_ref(v_x_3707_);
    return v_res_3709_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(
    mut v_00_u03b2_3710_: *mut crate::leanh::LeanObject,
    mut v_x_3711_: *mut crate::leanh::LeanObject,
    mut v_x_3712_: usize,
    mut v_x_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_3711_);
    v___x_3714_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg(v_x_3711_, v_x_3712_, v_x_3713_);
    return v___x_3714_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___boxed(
    mut v_00_u03b2_3715_: *mut crate::leanh::LeanObject,
    mut v_x_3716_: *mut crate::leanh::LeanObject,
    mut v_x_3717_: *mut crate::leanh::LeanObject,
    mut v_x_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2255__boxed_3719_: usize = 0;
    let mut v_res_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2255__boxed_3719_ = crate::leanh::lean_unbox_usize(v_x_3717_);
    crate::leanh::lean_dec(v_x_3717_);
    v_res_3720_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0(v_00_u03b2_3715_, v_x_3716_, v_x_2255__boxed_3719_, v_x_3718_);
    crate::leanh::lean_dec_ref(v_x_3716_);
    return v_res_3720_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3721_: *mut crate::leanh::LeanObject,
    mut v_keys_3722_: *mut crate::leanh::LeanObject,
    mut v_vals_3723_: *mut crate::leanh::LeanObject,
    mut v_heq_3724_: *mut crate::leanh::LeanObject,
    mut v_i_3725_: *mut crate::leanh::LeanObject,
    mut v_k_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___redArg(v_keys_3722_, v_vals_3723_, v_i_3725_, v_k_3726_);
    return v___x_3727_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3728_: *mut crate::leanh::LeanObject,
    mut v_keys_3729_: *mut crate::leanh::LeanObject,
    mut v_vals_3730_: *mut crate::leanh::LeanObject,
    mut v_heq_3731_: *mut crate::leanh::LeanObject,
    mut v_i_3732_: *mut crate::leanh::LeanObject,
    mut v_k_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3734_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0_spec__1(v_00_u03b2_3728_, v_keys_3729_, v_vals_3730_, v_heq_3731_, v_i_3732_, v_k_3733_);
    crate::leanh::lean_dec_ref(v_vals_3730_);
    crate::leanh::lean_dec_ref(v_keys_3729_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___redArg(
    mut v_e_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3749_: u8 = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3770_: u8 = 0;
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_unused_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3738_ = lean_st_ref_take(v_a_3736_);
                v_share_3739_ = crate::leanh::lean_ctor_get(v___x_3738_, 0);
                v_maxFVar_3740_ = crate::leanh::lean_ctor_get(v___x_3738_, 1);
                v_proofInstInfo_3741_ = crate::leanh::lean_ctor_get(v___x_3738_, 2);
                v_inferType_3742_ = crate::leanh::lean_ctor_get(v___x_3738_, 3);
                v_getLevel_3743_ = crate::leanh::lean_ctor_get(v___x_3738_, 4);
                v_congrInfo_3744_ = crate::leanh::lean_ctor_get(v___x_3738_, 5);
                v_defEqI_3745_ = crate::leanh::lean_ctor_get(v___x_3738_, 6);
                v_extensions_3746_ = crate::leanh::lean_ctor_get(v___x_3738_, 7);
                v_issues_3747_ = crate::leanh::lean_ctor_get(v___x_3738_, 8);
                v_canon_3748_ = crate::leanh::lean_ctor_get(v___x_3738_, 9);
                v_debug_3749_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3738_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3782_ = (!crate::leanh::lean_is_exclusive(v___x_3738_)) as u8;
                if v_isSharedCheck_3782_ == 0 {
                    v___x_3751_ = v___x_3738_;
                    v_isShared_3752_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3748_);
                    crate::leanh::lean_inc(v_issues_3747_);
                    crate::leanh::lean_inc(v_extensions_3746_);
                    crate::leanh::lean_inc(v_defEqI_3745_);
                    crate::leanh::lean_inc(v_congrInfo_3744_);
                    crate::leanh::lean_inc(v_getLevel_3743_);
                    crate::leanh::lean_inc(v_inferType_3742_);
                    crate::leanh::lean_inc(v_proofInstInfo_3741_);
                    crate::leanh::lean_inc(v_maxFVar_3740_);
                    crate::leanh::lean_inc(v_share_3739_);
                    crate::leanh::lean_dec(v___x_3738_);
                    v___x_3751_ = crate::leanh::lean_box(0);
                    v_isShared_3752_ = v_isSharedCheck_3782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3753_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_SymM_run___redArg___closed__0_once),
                    _init_l_Lean_Meta_Sym_SymM_run___redArg___closed__0,
                );
                if v_isShared_3752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3751_, 0, v___x_3753_);
                    v___x_3755_ = v___x_3751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_maxFVar_3740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_proofInstInfo_3741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_inferType_3742_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_getLevel_3743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 5, v_congrInfo_3744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 6, v_defEqI_3745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 7, v_extensions_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 8, v_issues_3747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 9, v_canon_3748_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3781_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
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
                v_fst_3758_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                crate::leanh::lean_inc(v_fst_3758_);
                v_snd_3759_ = crate::leanh::lean_ctor_get(v___x_3757_, 1);
                crate::leanh::lean_inc(v_snd_3759_);
                crate::leanh::lean_dec_ref(v___x_3757_);
                v___x_3760_ = lean_st_ref_take(v_a_3736_);
                v_maxFVar_3761_ = crate::leanh::lean_ctor_get(v___x_3760_, 1);
                v_proofInstInfo_3762_ = crate::leanh::lean_ctor_get(v___x_3760_, 2);
                v_inferType_3763_ = crate::leanh::lean_ctor_get(v___x_3760_, 3);
                v_getLevel_3764_ = crate::leanh::lean_ctor_get(v___x_3760_, 4);
                v_congrInfo_3765_ = crate::leanh::lean_ctor_get(v___x_3760_, 5);
                v_defEqI_3766_ = crate::leanh::lean_ctor_get(v___x_3760_, 6);
                v_extensions_3767_ = crate::leanh::lean_ctor_get(v___x_3760_, 7);
                v_issues_3768_ = crate::leanh::lean_ctor_get(v___x_3760_, 8);
                v_canon_3769_ = crate::leanh::lean_ctor_get(v___x_3760_, 9);
                v_debug_3770_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3779_ = (!crate::leanh::lean_is_exclusive(v___x_3760_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v_unused_3780_ = crate::leanh::lean_ctor_get(v___x_3760_, 0);
                    crate::leanh::lean_dec(v_unused_3780_);
                    v___x_3772_ = v___x_3760_;
                    v_isShared_3773_ = v_isSharedCheck_3779_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3769_);
                    crate::leanh::lean_inc(v_issues_3768_);
                    crate::leanh::lean_inc(v_extensions_3767_);
                    crate::leanh::lean_inc(v_defEqI_3766_);
                    crate::leanh::lean_inc(v_congrInfo_3765_);
                    crate::leanh::lean_inc(v_getLevel_3764_);
                    crate::leanh::lean_inc(v_inferType_3763_);
                    crate::leanh::lean_inc(v_proofInstInfo_3762_);
                    crate::leanh::lean_inc(v_maxFVar_3761_);
                    crate::leanh::lean_dec(v___x_3760_);
                    v___x_3772_ = crate::leanh::lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3779_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3772_, 0, v_snd_3759_);
                    v___x_3775_ = v___x_3772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_snd_3759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_maxFVar_3761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_proofInstInfo_3762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_inferType_3763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_getLevel_3764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 5, v_congrInfo_3765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_defEqI_3766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_extensions_3767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_issues_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 9, v_canon_3769_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3778_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_3770_,
                    );
                    v___x_3775_ = v_reuseFailAlloc_3778_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3776_ = lean_st_ref_set(v_a_3736_, v___x_3775_);
                v___x_3777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3777_, 0, v_fst_3758_);
                return v___x_3777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___redArg___boxed(
    mut v_e_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3786_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3783_, v_a_3784_);
    crate::leanh::lean_dec(v_a_3784_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc(
    mut v_e_3787_: *mut crate::leanh::LeanObject,
    mut v_a_3788_: *mut crate::leanh::LeanObject,
    mut v_a_3789_: *mut crate::leanh::LeanObject,
    mut v_a_3790_: *mut crate::leanh::LeanObject,
    mut v_a_3791_: *mut crate::leanh::LeanObject,
    mut v_a_3792_: *mut crate::leanh::LeanObject,
    mut v_a_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3787_, v_a_3789_);
    return v___x_3795_;
}
pub unsafe fn l_Lean_Meta_Sym_shareCommonInc___boxed(
    mut v_e_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l_Lean_Meta_Sym_shareCommonInc(
        v_e_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_,
    );
    crate::leanh::lean_dec(v_a_3802_);
    crate::leanh::lean_dec_ref(v_a_3801_);
    crate::leanh::lean_dec(v_a_3800_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    crate::leanh::lean_dec(v_a_3798_);
    crate::leanh::lean_dec_ref(v_a_3797_);
    return v_res_3804_;
}
pub unsafe fn l_Lean_Meta_Sym_share___redArg(
    mut v_e_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3808_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3805_, v_a_3806_);
    return v___x_3808_;
}
pub unsafe fn l_Lean_Meta_Sym_share___redArg___boxed(
    mut v_e_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Lean_Meta_Sym_share___redArg(v_e_3809_, v_a_3810_);
    crate::leanh::lean_dec(v_a_3810_);
    return v_res_3812_;
}
pub unsafe fn l_Lean_Meta_Sym_share(
    mut v_e_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_e_3813_, v_a_3815_);
    return v___x_3821_;
}
pub unsafe fn l_Lean_Meta_Sym_share___boxed(
    mut v_e_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
    mut v_a_3827_: *mut crate::leanh::LeanObject,
    mut v_a_3828_: *mut crate::leanh::LeanObject,
    mut v_a_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3830_ = l_Lean_Meta_Sym_share(
        v_e_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_,
    );
    crate::leanh::lean_dec(v_a_3828_);
    crate::leanh::lean_dec_ref(v_a_3827_);
    crate::leanh::lean_dec(v_a_3826_);
    crate::leanh::lean_dec_ref(v_a_3825_);
    crate::leanh::lean_dec(v_a_3824_);
    crate::leanh::lean_dec_ref(v_a_3823_);
    return v_res_3830_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___redArg(
    mut v_a_3831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3834_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = lean_st_ref_get(v_a_3831_);
    v_debug_3834_ = crate::leanh::lean_ctor_get_uint8(
        v___x_3833_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
    );
    crate::leanh::lean_dec(v___x_3833_);
    v___x_3835_ = crate::leanh::lean_box((v_debug_3834_) as usize);
    v___x_3836_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3836_, 0, v___x_3835_);
    return v___x_3836_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___redArg___boxed(
    mut v_a_3837_: *mut crate::leanh::LeanObject,
    mut v_a_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3839_ = l_Lean_Meta_Sym_isDebugEnabled___redArg(v_a_3837_);
    crate::leanh::lean_dec(v_a_3837_);
    return v_res_3839_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled(
    mut v_a_3840_: *mut crate::leanh::LeanObject,
    mut v_a_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3848_: u8 = 0;
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = lean_st_ref_get(v_a_3841_);
    v_debug_3848_ = crate::leanh::lean_ctor_get_uint8(
        v___x_3847_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
    );
    crate::leanh::lean_dec(v___x_3847_);
    v___x_3849_ = crate::leanh::lean_box((v_debug_3848_) as usize);
    v___x_3850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3850_, 0, v___x_3849_);
    return v___x_3850_;
}
pub unsafe fn l_Lean_Meta_Sym_isDebugEnabled___boxed(
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3858_ = l_Lean_Meta_Sym_isDebugEnabled(
        v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_,
    );
    crate::leanh::lean_dec(v_a_3856_);
    crate::leanh::lean_dec_ref(v_a_3855_);
    crate::leanh::lean_dec(v_a_3854_);
    crate::leanh::lean_dec_ref(v_a_3853_);
    crate::leanh::lean_dec(v_a_3852_);
    crate::leanh::lean_dec_ref(v_a_3851_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___redArg(
    mut v_a_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_3861_: u8 = 0;
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_config_3861_ = crate::leanh::lean_ctor_get_uint8(
        v_a_3859_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_3862_ = crate::leanh::lean_box((v_config_3861_) as usize);
    v___x_3863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3863_, 0, v___x_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___redArg___boxed(
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_a_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3866_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3864_);
    crate::leanh::lean_dec_ref(v_a_3864_);
    return v_res_3866_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig(
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
    mut v_a_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3867_);
    return v___x_3874_;
}
pub unsafe fn l_Lean_Meta_Sym_getConfig___boxed(
    mut v_a_3875_: *mut crate::leanh::LeanObject,
    mut v_a_3876_: *mut crate::leanh::LeanObject,
    mut v_a_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_a_3879_: *mut crate::leanh::LeanObject,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
    mut v_a_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3882_ = l_Lean_Meta_Sym_getConfig(
        v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_,
    );
    crate::leanh::lean_dec(v_a_3880_);
    crate::leanh::lean_dec_ref(v_a_3879_);
    crate::leanh::lean_dec(v_a_3878_);
    crate::leanh::lean_dec_ref(v_a_3877_);
    crate::leanh::lean_dec(v_a_3876_);
    crate::leanh::lean_dec_ref(v_a_3875_);
    return v_res_3882_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
    mut v_msgData_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = lean_st_ref_get(v___y_3887_);
    v_env_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
    crate::leanh::lean_inc_ref(v_env_3890_);
    crate::leanh::lean_dec(v___x_3889_);
    v___x_3891_ = lean_st_ref_get(v___y_3885_);
    v_mctx_3892_ = crate::leanh::lean_ctor_get(v___x_3891_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3892_);
    crate::leanh::lean_dec(v___x_3891_);
    v_lctx_3893_ = crate::leanh::lean_ctor_get(v___y_3884_, 2);
    v_options_3894_ = crate::leanh::lean_ctor_get(v___y_3886_, 2);
    crate::leanh::lean_inc_ref(v_options_3894_);
    crate::leanh::lean_inc_ref(v_lctx_3893_);
    v___x_3895_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3895_, 0, v_env_3890_);
    crate::leanh::lean_ctor_set(v___x_3895_, 1, v_mctx_3892_);
    crate::leanh::lean_ctor_set(v___x_3895_, 2, v_lctx_3893_);
    crate::leanh::lean_ctor_set(v___x_3895_, 3, v_options_3894_);
    v___x_3896_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3896_, 0, v___x_3895_);
    crate::leanh::lean_ctor_set(v___x_3896_, 1, v_msgData_3883_);
    v___x_3897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3897_, 0, v___x_3896_);
    return v___x_3897_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0___boxed(
    mut v_msgData_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
        v_msgData_3898_,
        v___y_3899_,
        v___y_3900_,
        v___y_3901_,
        v___y_3902_,
    );
    crate::leanh::lean_dec(v___y_3902_);
    crate::leanh::lean_dec_ref(v___y_3901_);
    crate::leanh::lean_dec(v___y_3900_);
    crate::leanh::lean_dec_ref(v___y_3899_);
    return v_res_3904_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: f64 = 0.0;
    v___x_3905_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3906_ = lean_float_of_nat(v___x_3905_);
    return v___x_3906_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
    mut v_cls_3910_: *mut crate::leanh::LeanObject,
    mut v_msg_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v_tid_3936_: u64 = 0;
    let mut v_traces_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: f64 = 0.0;
    let mut v___x_3943_: u8 = 0;
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3961_: u8 = 0;
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3917_ = crate::leanh::lean_ctor_get(v___y_3914_, 5);
                v___x_3918_ =
                    l_Lean_addMessageContextFull___at___00Lean_Meta_Sym_reportIssue_spec__0(
                        v_msg_3911_,
                        v___y_3912_,
                        v___y_3913_,
                        v___y_3914_,
                        v___y_3915_,
                    );
                v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3918_, 0);
                v_isSharedCheck_3963_ = (!crate::leanh::lean_is_exclusive(v___x_3918_)) as u8;
                if v_isSharedCheck_3963_ == 0 {
                    v___x_3921_ = v___x_3918_;
                    v_isShared_3922_ = v_isSharedCheck_3963_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3919_);
                    crate::leanh::lean_dec(v___x_3918_);
                    v___x_3921_ = crate::leanh::lean_box(0);
                    v_isShared_3922_ = v_isSharedCheck_3963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3923_ = lean_st_ref_take(v___y_3915_);
                v_traceState_3924_ = crate::leanh::lean_ctor_get(v___x_3923_, 4);
                v_env_3925_ = crate::leanh::lean_ctor_get(v___x_3923_, 0);
                v_nextMacroScope_3926_ = crate::leanh::lean_ctor_get(v___x_3923_, 1);
                v_ngen_3927_ = crate::leanh::lean_ctor_get(v___x_3923_, 2);
                v_auxDeclNGen_3928_ = crate::leanh::lean_ctor_get(v___x_3923_, 3);
                v_cache_3929_ = crate::leanh::lean_ctor_get(v___x_3923_, 5);
                v_messages_3930_ = crate::leanh::lean_ctor_get(v___x_3923_, 6);
                v_infoState_3931_ = crate::leanh::lean_ctor_get(v___x_3923_, 7);
                v_snapshotTasks_3932_ = crate::leanh::lean_ctor_get(v___x_3923_, 8);
                v_isSharedCheck_3962_ = (!crate::leanh::lean_is_exclusive(v___x_3923_)) as u8;
                if v_isSharedCheck_3962_ == 0 {
                    v___x_3934_ = v___x_3923_;
                    v_isShared_3935_ = v_isSharedCheck_3962_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3932_);
                    crate::leanh::lean_inc(v_infoState_3931_);
                    crate::leanh::lean_inc(v_messages_3930_);
                    crate::leanh::lean_inc(v_cache_3929_);
                    crate::leanh::lean_inc(v_traceState_3924_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3928_);
                    crate::leanh::lean_inc(v_ngen_3927_);
                    crate::leanh::lean_inc(v_nextMacroScope_3926_);
                    crate::leanh::lean_inc(v_env_3925_);
                    crate::leanh::lean_dec(v___x_3923_);
                    v___x_3934_ = crate::leanh::lean_box(0);
                    v_isShared_3935_ = v_isSharedCheck_3962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3936_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3924_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3937_ = crate::leanh::lean_ctor_get(v_traceState_3924_, 0);
                v_isSharedCheck_3961_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3924_)) as u8;
                if v_isSharedCheck_3961_ == 0 {
                    v___x_3939_ = v_traceState_3924_;
                    v_isShared_3940_ = v_isSharedCheck_3961_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3937_);
                    crate::leanh::lean_dec(v_traceState_3924_);
                    v___x_3939_ = crate::leanh::lean_box(0);
                    v_isShared_3940_ = v_isSharedCheck_3961_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3941_ = crate::leanh::lean_box(0);
                v___x_3942_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0);
                v___x_3943_ = 0;
                v___x_3944_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
                v___x_3945_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3945_, 0, v_cls_3910_);
                crate::leanh::lean_ctor_set(v___x_3945_, 1, v___x_3941_);
                crate::leanh::lean_ctor_set(v___x_3945_, 2, v___x_3944_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3942_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3942_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3945_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3943_,
                );
                v___x_3946_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2;
                v___x_3947_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3947_, 0, v___x_3945_);
                crate::leanh::lean_ctor_set(v___x_3947_, 1, v_a_3919_);
                crate::leanh::lean_ctor_set(v___x_3947_, 2, v___x_3946_);
                crate::leanh::lean_inc(v_ref_3917_);
                v___x_3948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3948_, 0, v_ref_3917_);
                crate::leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = l_Lean_PersistentArray_push___redArg(v_traces_3937_, v___x_3948_);
                if v_isShared_3940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3939_, 0, v___x_3949_);
                    v___x_3951_ = v___x_3939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3960_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3949_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3960_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3936_,
                    );
                    v___x_3951_ = v_reuseFailAlloc_3960_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3934_, 4, v___x_3951_);
                    v___x_3953_ = v___x_3934_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_env_3925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 1, v_nextMacroScope_3926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 2, v_ngen_3927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 3, v_auxDeclNGen_3928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 4, v___x_3951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 5, v_cache_3929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 6, v_messages_3930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 7, v_infoState_3931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 8, v_snapshotTasks_3932_);
                    v___x_3953_ = v_reuseFailAlloc_3959_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3954_ = lean_st_ref_set(v___y_3915_, v___x_3953_);
                v___x_3955_ = crate::leanh::lean_box(0);
                if v_isShared_3922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3921_, 0, v___x_3955_);
                    v___x_3957_ = v___x_3921_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
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
    mut v_cls_3964_: *mut crate::leanh::LeanObject,
    mut v_msg_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg(
        v_cls_3964_,
        v_msg_3965_,
        v___y_3966_,
        v___y_3967_,
        v___y_3968_,
        v___y_3969_,
    );
    crate::leanh::lean_dec(v___y_3969_);
    crate::leanh::lean_dec_ref(v___y_3968_);
    crate::leanh::lean_dec(v___y_3967_);
    crate::leanh::lean_dec_ref(v___y_3966_);
    return v_res_3971_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_reportIssue___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: u8 = 0;
    let mut v___x_3977_: f64 = 0.0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
    v___x_3976_ = 1;
    v___x_3977_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__0,
    );
    v___x_3978_ = crate::leanh::lean_box(0);
    v___x_3979_ = l_Lean_Meta_Sym_reportIssue___closed__1;
    v___x_3980_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
    crate::leanh::lean_ctor_set(v___x_3980_, 1, v___x_3978_);
    crate::leanh::lean_ctor_set(v___x_3980_, 2, v___x_3975_);
    crate::leanh::lean_ctor_set_float(
        v___x_3980_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_3977_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_3980_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_3977_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3980_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_3976_,
    );
    return v___x_3980_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_reportIssue___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3984_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
    v___x_3985_ = l_Lean_Meta_Sym_reportIssue___closed__4;
    v___x_3986_ = l_Lean_Name_append(v___x_3985_, v___x_3984_);
    return v___x_3986_;
}
pub unsafe fn l_Lean_Meta_Sym_reportIssue(
    mut v_msg_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4011_: u8 = 0;
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4023_: u8 = 0;
    let mut v_inheritedTraceOptions_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                v_a_3999_ = crate::leanh::lean_ctor_get(v___x_3998_, 0);
                crate::leanh::lean_inc(v_a_3999_);
                crate::leanh::lean_dec_ref(v___x_3998_);
                v___x_4000_ = lean_st_ref_take(v_a_3989_);
                v_share_4001_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                v_maxFVar_4002_ = crate::leanh::lean_ctor_get(v___x_4000_, 1);
                v_proofInstInfo_4003_ = crate::leanh::lean_ctor_get(v___x_4000_, 2);
                v_inferType_4004_ = crate::leanh::lean_ctor_get(v___x_4000_, 3);
                v_getLevel_4005_ = crate::leanh::lean_ctor_get(v___x_4000_, 4);
                v_congrInfo_4006_ = crate::leanh::lean_ctor_get(v___x_4000_, 5);
                v_defEqI_4007_ = crate::leanh::lean_ctor_get(v___x_4000_, 6);
                v_extensions_4008_ = crate::leanh::lean_ctor_get(v___x_4000_, 7);
                v_issues_4009_ = crate::leanh::lean_ctor_get(v___x_4000_, 8);
                v_canon_4010_ = crate::leanh::lean_ctor_get(v___x_4000_, 9);
                v_debug_4011_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4000_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4030_ = (!crate::leanh::lean_is_exclusive(v___x_4000_)) as u8;
                if v_isSharedCheck_4030_ == 0 {
                    v___x_4013_ = v___x_4000_;
                    v_isShared_4014_ = v_isSharedCheck_4030_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4010_);
                    crate::leanh::lean_inc(v_issues_4009_);
                    crate::leanh::lean_inc(v_extensions_4008_);
                    crate::leanh::lean_inc(v_defEqI_4007_);
                    crate::leanh::lean_inc(v_congrInfo_4006_);
                    crate::leanh::lean_inc(v_getLevel_4005_);
                    crate::leanh::lean_inc(v_inferType_4004_);
                    crate::leanh::lean_inc(v_proofInstInfo_4003_);
                    crate::leanh::lean_inc(v_maxFVar_4002_);
                    crate::leanh::lean_inc(v_share_4001_);
                    crate::leanh::lean_dec(v___x_4000_);
                    v___x_4013_ = crate::leanh::lean_box(0);
                    v_isShared_4014_ = v_isSharedCheck_4030_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3996_ = crate::leanh::lean_box(0);
                v___x_3997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3997_, 0, v___x_3996_);
                return v___x_3997_;
            }
            2 => {
                v___x_4015_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_reportIssue___closed__2_once),
                    _init_l_Lean_Meta_Sym_reportIssue___closed__2,
                );
                v___x_4016_ =
                    l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__2;
                crate::leanh::lean_inc(v_a_3999_);
                v___x_4017_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4017_, 0, v___x_4015_);
                crate::leanh::lean_ctor_set(v___x_4017_, 1, v_a_3999_);
                crate::leanh::lean_ctor_set(v___x_4017_, 2, v___x_4016_);
                v___x_4018_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4018_, 0, v___x_4017_);
                crate::leanh::lean_ctor_set(v___x_4018_, 1, v_issues_4009_);
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 8, v___x_4018_);
                    v___x_4020_ = v___x_4013_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4029_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_share_4001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_maxFVar_4002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 2, v_proofInstInfo_4003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 3, v_inferType_4004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 4, v_getLevel_4005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 5, v_congrInfo_4006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 6, v_defEqI_4007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 7, v_extensions_4008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 8, v___x_4018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 9, v_canon_4010_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4029_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4011_,
                    );
                    v___x_4020_ = v_reuseFailAlloc_4029_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4021_ = lean_st_ref_set(v_a_3989_, v___x_4020_);
                v_options_4022_ = crate::leanh::lean_ctor_get(v_a_3992_, 2);
                v_hasTrace_4023_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4023_ == 0 {
                    crate::leanh::lean_dec(v_a_3999_);
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_4024_ = crate::leanh::lean_ctor_get(v_a_3992_, 13);
                    v___x_4025_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn___closed__1_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_;
                    v___x_4026_ = crate::leanh::lean_obj_once(
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
                        crate::leanh::lean_dec(v_a_3999_);
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
    mut v_msg_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
    mut v_a_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Lean_Meta_Sym_reportIssue(
        v_msg_4031_,
        v_a_4032_,
        v_a_4033_,
        v_a_4034_,
        v_a_4035_,
        v_a_4036_,
        v_a_4037_,
    );
    crate::leanh::lean_dec(v_a_4037_);
    crate::leanh::lean_dec_ref(v_a_4036_);
    crate::leanh::lean_dec(v_a_4035_);
    crate::leanh::lean_dec_ref(v_a_4034_);
    crate::leanh::lean_dec(v_a_4033_);
    crate::leanh::lean_dec_ref(v_a_4032_);
    return v_res_4039_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1(
    mut v_cls_4040_: *mut crate::leanh::LeanObject,
    mut v_msg_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cls_4050_: *mut crate::leanh::LeanObject,
    mut v_msg_4051_: *mut crate::leanh::LeanObject,
    mut v___y_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_4057_);
    crate::leanh::lean_dec_ref(v___y_4056_);
    crate::leanh::lean_dec(v___y_4055_);
    crate::leanh::lean_dec_ref(v___y_4054_);
    crate::leanh::lean_dec(v___y_4053_);
    crate::leanh::lean_dec_ref(v___y_4052_);
    return v_res_4059_;
}
pub unsafe fn l_Lean_Meta_Sym_reportIssueIfVerbose(
    mut v_msg_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4068_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4061_);
                v_a_4069_ = crate::leanh::lean_ctor_get(v___x_4068_, 0);
                v_isSharedCheck_4079_ = (!crate::leanh::lean_is_exclusive(v___x_4068_)) as u8;
                if v_isSharedCheck_4079_ == 0 {
                    v___x_4071_ = v___x_4068_;
                    v_isShared_4072_ = v_isSharedCheck_4079_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4069_);
                    crate::leanh::lean_dec(v___x_4068_);
                    v___x_4071_ = crate::leanh::lean_box(0);
                    v_isShared_4072_ = v_isSharedCheck_4079_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4073_ = (crate::leanh::lean_unbox(v_a_4069_) as u8);
                crate::leanh::lean_dec(v_a_4069_);
                if v___x_4073_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_4060_);
                    v___x_4074_ = crate::leanh::lean_box(0);
                    if v_isShared_4072_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4071_, 0, v___x_4074_);
                        v___x_4076_ = v___x_4071_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4077_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4074_);
                        v___x_4076_ = v_reuseFailAlloc_4077_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4071_);
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
    mut v_msg_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_Lean_Meta_Sym_reportIssueIfVerbose(
        v_msg_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
        v_a_4084_,
        v_a_4085_,
        v_a_4086_,
    );
    crate::leanh::lean_dec(v_a_4086_);
    crate::leanh::lean_dec_ref(v_a_4085_);
    crate::leanh::lean_dec(v_a_4084_);
    crate::leanh::lean_dec_ref(v_a_4083_);
    crate::leanh::lean_dec(v_a_4082_);
    crate::leanh::lean_dec_ref(v_a_4081_);
    return v_res_4088_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4104_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__6;
    v___x_4105_ = l_String_toRawSubstring_x27(v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4143_ = l_Lean_addTrace___at___00Lean_Meta_Sym_reportIssue_spec__1___redArg___closed__1;
    v___x_4144_ = l_String_toRawSubstring_x27(v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__29;
    v___x_4157_ = l_String_toRawSubstring_x27(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
    mut v_s_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msg_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: u8 = 0;
    let mut v_quotContext_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_s_4180_);
                v___x_4203_ = l_Lean_Syntax_getKind(v_s_4180_);
                v___x_4204_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16;
                v___x_4205_ = lean_name_eq(v___x_4203_, v___x_4204_);
                crate::leanh::lean_dec(v___x_4203_);
                if v___x_4205_ == 0 {
                    v_quotContext_4206_ = crate::leanh::lean_ctor_get(v_a_4181_, 1);
                    v_currMacroScope_4207_ = crate::leanh::lean_ctor_get(v_a_4181_, 2);
                    v_ref_4208_ = crate::leanh::lean_ctor_get(v_a_4181_, 5);
                    v___x_4209_ = l_Lean_SourceInfo_fromRef(v_ref_4208_, v___x_4205_);
                    v___x_4210_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18;
                    v___x_4211_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20;
                    v___x_4212_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21;
                    crate::leanh::lean_inc_n(v___x_4209_, 8);
                    v___x_4213_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4213_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                    v___x_4214_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23;
                    v___x_4215_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
                    v___x_4216_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_n(v_currMacroScope_4207_, 3);
                    crate::leanh::lean_inc_n(v_quotContext_4206_, 3);
                    v___x_4217_ = l_Lean_addMacroScope(
                        v_quotContext_4206_,
                        v___x_4216_,
                        v_currMacroScope_4207_,
                    );
                    v___x_4218_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27;
                    v___x_4219_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4219_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v___x_4219_, 1, v___x_4215_);
                    crate::leanh::lean_ctor_set(v___x_4219_, 2, v___x_4217_);
                    crate::leanh::lean_ctor_set(v___x_4219_, 3, v___x_4218_);
                    v___x_4220_ = l_Lean_Syntax_node1(v___x_4209_, v___x_4214_, v___x_4219_);
                    v___x_4221_ =
                        l_Lean_Syntax_node2(v___x_4209_, v___x_4211_, v___x_4213_, v___x_4220_);
                    v___x_4222_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28;
                    v___x_4223_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4223_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                    v___x_4224_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                    v___x_4225_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
                    v___x_4226_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31;
                    v___x_4227_ = l_Lean_addMacroScope(
                        v_quotContext_4206_,
                        v___x_4226_,
                        v_currMacroScope_4207_,
                    );
                    v___x_4228_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36;
                    v___x_4229_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4229_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v___x_4229_, 1, v___x_4225_);
                    crate::leanh::lean_ctor_set(v___x_4229_, 2, v___x_4227_);
                    crate::leanh::lean_ctor_set(v___x_4229_, 3, v___x_4228_);
                    v___x_4230_ = l_Lean_Syntax_node1(v___x_4209_, v___x_4224_, v___x_4229_);
                    v___x_4231_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37;
                    v___x_4232_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4232_, 0, v___x_4209_);
                    crate::leanh::lean_ctor_set(v___x_4232_, 1, v___x_4231_);
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
                    v_quotContext_4234_ = crate::leanh::lean_ctor_get(v_a_4181_, 1);
                    v_currMacroScope_4235_ = crate::leanh::lean_ctor_get(v_a_4181_, 2);
                    v_ref_4236_ = crate::leanh::lean_ctor_get(v_a_4181_, 5);
                    v___x_4237_ = 0;
                    v___x_4238_ = l_Lean_SourceInfo_fromRef(v_ref_4236_, v___x_4237_);
                    v___x_4239_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39;
                    v___x_4240_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40;
                    crate::leanh::lean_inc(v___x_4238_);
                    v___x_4241_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4241_, 0, v___x_4238_);
                    crate::leanh::lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                    v___x_4242_ =
                        l_Lean_Syntax_node2(v___x_4238_, v___x_4239_, v___x_4241_, v_s_4180_);
                    crate::leanh::lean_inc(v_currMacroScope_4235_);
                    crate::leanh::lean_inc(v_quotContext_4234_);
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
                v___x_4193_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__7);
                v___x_4194_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__9;
                v___x_4195_ =
                    l_Lean_addMacroScope(v_quotContext_4185_, v___x_4194_, v_currMacroScope_4186_);
                v___x_4196_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__12;
                crate::leanh::lean_inc_n(v___x_4190_, 3);
                v___x_4197_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4197_, 0, v___x_4190_);
                crate::leanh::lean_ctor_set(v___x_4197_, 1, v___x_4193_);
                crate::leanh::lean_ctor_set(v___x_4197_, 2, v___x_4195_);
                crate::leanh::lean_ctor_set(v___x_4197_, 3, v___x_4196_);
                v___x_4198_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                v___x_4199_ = l_Lean_Syntax_node1(v___x_4190_, v___x_4198_, v_msg_4184_);
                v___x_4200_ =
                    l_Lean_Syntax_node2(v___x_4190_, v___x_4192_, v___x_4197_, v___x_4199_);
                v___x_4201_ = l_Lean_Syntax_node1(v___x_4190_, v___x_4191_, v___x_4200_);
                v___x_4202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4202_, 0, v___x_4201_);
                crate::leanh::lean_ctor_set(v___x_4202_, 1, v___y_4188_);
                return v___x_4202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___boxed(
    mut v_s_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4246_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
        v_s_4243_, v_a_4244_, v_a_4245_,
    );
    crate::leanh::lean_dec_ref(v_a_4244_);
    return v_res_4246_;
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(
    mut v_x_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4290_ = l_Lean_Meta_Sym_doElemReportIssue_x21_____00__closed__1;
                crate::leanh::lean_inc(v_x_4287_);
                v___x_4291_ = l_Lean_Syntax_isOfKind(v_x_4287_, v___x_4290_);
                if v___x_4291_ == 0 {
                    crate::leanh::lean_dec(v_x_4287_);
                    v___x_4292_ = crate::leanh::lean_box(1);
                    v___x_4293_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4293_, 0, v___x_4292_);
                    crate::leanh::lean_ctor_set(v___x_4293_, 1, v_a_4289_);
                    return v___x_4293_;
                } else {
                    v___x_4294_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4295_ = l_Lean_Syntax_getArg(v_x_4287_, v___x_4294_);
                    crate::leanh::lean_dec(v_x_4287_);
                    v___x_4296_ =
                        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro(
                            v___x_4295_,
                            v_a_4288_,
                            v_a_4289_,
                        );
                    v_a_4297_ = crate::leanh::lean_ctor_get(v___x_4296_, 0);
                    v_a_4298_ = crate::leanh::lean_ctor_get(v___x_4296_, 1);
                    v_isSharedCheck_4305_ = (!crate::leanh::lean_is_exclusive(v___x_4296_)) as u8;
                    if v_isSharedCheck_4305_ == 0 {
                        v___x_4300_ = v___x_4296_;
                        v_isShared_4301_ = v_isSharedCheck_4305_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4298_);
                        crate::leanh::lean_inc(v_a_4297_);
                        crate::leanh::lean_dec(v___x_4296_);
                        v___x_4300_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_a_4298_);
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
    mut v_x_4306_: *mut crate::leanh::LeanObject,
    mut v_a_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4309_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportIssue_x21______1(v_x_4306_, v_a_4307_, v_a_4308_);
    crate::leanh::lean_dec_ref(v_a_4307_);
    return v_res_4309_;
}
pub unsafe fn l_Lean_Meta_Sym_reportDbgIssue(
    mut v_msg_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4323_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4318_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_4311_);
                v_a_4319_ = crate::leanh::lean_ctor_get(v___x_4318_, 0);
                v_isSharedCheck_4338_ = (!crate::leanh::lean_is_exclusive(v___x_4318_)) as u8;
                if v_isSharedCheck_4338_ == 0 {
                    v___x_4321_ = v___x_4318_;
                    v_isShared_4322_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4319_);
                    crate::leanh::lean_dec(v___x_4318_);
                    v___x_4321_ = crate::leanh::lean_box(0);
                    v_isShared_4322_ = v_isSharedCheck_4338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4323_ = (crate::leanh::lean_unbox(v_a_4319_) as u8);
                crate::leanh::lean_dec(v_a_4319_);
                if v___x_4323_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_4310_);
                    v___x_4324_ = crate::leanh::lean_box(0);
                    if v_isShared_4322_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4321_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4321_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                        v___x_4326_ = v_reuseFailAlloc_4327_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_options_4328_ = crate::leanh::lean_ctor_get(v_a_4315_, 2);
                    v___x_4329_ = l_Lean_KVMap_instValueBool;
                    v___x_4330_ = l_Lean_Meta_Sym_sym_debug;
                    v___x_4331_ =
                        l_Lean_Option_get___redArg(v___x_4329_, v_options_4328_, v___x_4330_);
                    v___x_4332_ = (crate::leanh::lean_unbox(v___x_4331_) as u8);
                    crate::leanh::lean_dec(v___x_4331_);
                    if v___x_4332_ == 0 {
                        crate::leanh::lean_dec_ref(v_msg_4310_);
                        v___x_4333_ = crate::leanh::lean_box(0);
                        if v_isShared_4322_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4321_, 0, v___x_4333_);
                            v___x_4335_ = v___x_4321_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4336_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
                            v___x_4335_ = v_reuseFailAlloc_4336_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4321_);
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
    mut v_msg_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_a_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4347_ = l_Lean_Meta_Sym_reportDbgIssue(
        v_msg_4339_,
        v_a_4340_,
        v_a_4341_,
        v_a_4342_,
        v_a_4343_,
        v_a_4344_,
        v_a_4345_,
    );
    crate::leanh::lean_dec(v_a_4345_);
    crate::leanh::lean_dec_ref(v_a_4344_);
    crate::leanh::lean_dec(v_a_4343_);
    crate::leanh::lean_dec_ref(v_a_4342_);
    crate::leanh::lean_dec(v_a_4341_);
    crate::leanh::lean_dec_ref(v_a_4340_);
    return v_res_4347_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4349_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro___closed__0;
    v___x_4350_ = l_String_toRawSubstring_x27(v___x_4349_);
    return v___x_4350_;
}
pub unsafe fn l_Lean_Meta_Sym_expandReportDbgIssueMacro(
    mut v_s_4366_: *mut crate::leanh::LeanObject,
    mut v_a_4367_: *mut crate::leanh::LeanObject,
    mut v_a_4368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msg_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: u8 = 0;
    let mut v_quotContext_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_s_4366_);
                v___x_4389_ = l_Lean_Syntax_getKind(v_s_4366_);
                v___x_4390_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__16;
                v___x_4391_ = lean_name_eq(v___x_4389_, v___x_4390_);
                crate::leanh::lean_dec(v___x_4389_);
                if v___x_4391_ == 0 {
                    v_quotContext_4392_ = crate::leanh::lean_ctor_get(v_a_4367_, 1);
                    v_currMacroScope_4393_ = crate::leanh::lean_ctor_get(v_a_4367_, 2);
                    v_ref_4394_ = crate::leanh::lean_ctor_get(v_a_4367_, 5);
                    v___x_4395_ = l_Lean_SourceInfo_fromRef(v_ref_4394_, v___x_4391_);
                    v___x_4396_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__18;
                    v___x_4397_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__20;
                    v___x_4398_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__21;
                    crate::leanh::lean_inc_n(v___x_4395_, 8);
                    v___x_4399_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4399_, 0, v___x_4395_);
                    crate::leanh::lean_ctor_set(v___x_4399_, 1, v___x_4398_);
                    v___x_4400_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__23;
                    v___x_4401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__24);
                    v___x_4402_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_n(v_currMacroScope_4393_, 3);
                    crate::leanh::lean_inc_n(v_quotContext_4392_, 3);
                    v___x_4403_ = l_Lean_addMacroScope(
                        v_quotContext_4392_,
                        v___x_4402_,
                        v_currMacroScope_4393_,
                    );
                    v___x_4404_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__27;
                    v___x_4405_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4405_, 0, v___x_4395_);
                    crate::leanh::lean_ctor_set(v___x_4405_, 1, v___x_4401_);
                    crate::leanh::lean_ctor_set(v___x_4405_, 2, v___x_4403_);
                    crate::leanh::lean_ctor_set(v___x_4405_, 3, v___x_4404_);
                    v___x_4406_ = l_Lean_Syntax_node1(v___x_4395_, v___x_4400_, v___x_4405_);
                    v___x_4407_ =
                        l_Lean_Syntax_node2(v___x_4395_, v___x_4397_, v___x_4399_, v___x_4406_);
                    v___x_4408_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__28;
                    v___x_4409_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4395_);
                    crate::leanh::lean_ctor_set(v___x_4409_, 1, v___x_4408_);
                    v___x_4410_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                    v___x_4411_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30_once), _init_l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__30);
                    v___x_4412_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__31;
                    v___x_4413_ = l_Lean_addMacroScope(
                        v_quotContext_4392_,
                        v___x_4412_,
                        v_currMacroScope_4393_,
                    );
                    v___x_4414_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__36;
                    v___x_4415_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4415_, 0, v___x_4395_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 1, v___x_4411_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 2, v___x_4413_);
                    crate::leanh::lean_ctor_set(v___x_4415_, 3, v___x_4414_);
                    v___x_4416_ = l_Lean_Syntax_node1(v___x_4395_, v___x_4410_, v___x_4415_);
                    v___x_4417_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__37;
                    v___x_4418_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4418_, 0, v___x_4395_);
                    crate::leanh::lean_ctor_set(v___x_4418_, 1, v___x_4417_);
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
                    v_quotContext_4420_ = crate::leanh::lean_ctor_get(v_a_4367_, 1);
                    v_currMacroScope_4421_ = crate::leanh::lean_ctor_get(v_a_4367_, 2);
                    v_ref_4422_ = crate::leanh::lean_ctor_get(v_a_4367_, 5);
                    v___x_4423_ = 0;
                    v___x_4424_ = l_Lean_SourceInfo_fromRef(v_ref_4422_, v___x_4423_);
                    v___x_4425_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__39;
                    v___x_4426_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__40;
                    crate::leanh::lean_inc(v___x_4424_);
                    v___x_4427_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4427_, 0, v___x_4424_);
                    crate::leanh::lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                    v___x_4428_ =
                        l_Lean_Syntax_node2(v___x_4424_, v___x_4425_, v___x_4427_, v_s_4366_);
                    crate::leanh::lean_inc(v_currMacroScope_4421_);
                    crate::leanh::lean_inc(v_quotContext_4420_);
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
                v___x_4379_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc_n(v___x_4376_, 3);
                v___x_4383_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4383_, 0, v___x_4376_);
                crate::leanh::lean_ctor_set(v___x_4383_, 1, v___x_4379_);
                crate::leanh::lean_ctor_set(v___x_4383_, 2, v___x_4381_);
                crate::leanh::lean_ctor_set(v___x_4383_, 3, v___x_4382_);
                v___x_4384_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_expandReportIssueMacro___closed__14;
                v___x_4385_ = l_Lean_Syntax_node1(v___x_4376_, v___x_4384_, v_msg_4370_);
                v___x_4386_ =
                    l_Lean_Syntax_node2(v___x_4376_, v___x_4378_, v___x_4383_, v___x_4385_);
                v___x_4387_ = l_Lean_Syntax_node1(v___x_4376_, v___x_4377_, v___x_4386_);
                v___x_4388_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4388_, 0, v___x_4387_);
                crate::leanh::lean_ctor_set(v___x_4388_, 1, v___y_4374_);
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_expandReportDbgIssueMacro___boxed(
    mut v_s_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_a_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4432_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(v_s_4429_, v_a_4430_, v_a_4431_);
    crate::leanh::lean_dec_ref(v_a_4430_);
    return v_res_4432_;
}
pub unsafe fn l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(
    mut v_x_4451_: *mut crate::leanh::LeanObject,
    mut v_a_4452_: *mut crate::leanh::LeanObject,
    mut v_a_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4454_ = l_Lean_Meta_Sym_doElemReportDbgIssue_x21_____00__closed__1;
                crate::leanh::lean_inc(v_x_4451_);
                v___x_4455_ = l_Lean_Syntax_isOfKind(v_x_4451_, v___x_4454_);
                if v___x_4455_ == 0 {
                    crate::leanh::lean_dec(v_x_4451_);
                    v___x_4456_ = crate::leanh::lean_box(1);
                    v___x_4457_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4456_);
                    crate::leanh::lean_ctor_set(v___x_4457_, 1, v_a_4453_);
                    return v___x_4457_;
                } else {
                    v___x_4458_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4459_ = l_Lean_Syntax_getArg(v_x_4451_, v___x_4458_);
                    crate::leanh::lean_dec(v_x_4451_);
                    v___x_4460_ = l_Lean_Meta_Sym_expandReportDbgIssueMacro(
                        v___x_4459_,
                        v_a_4452_,
                        v_a_4453_,
                    );
                    v_a_4461_ = crate::leanh::lean_ctor_get(v___x_4460_, 0);
                    v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4460_, 1);
                    v_isSharedCheck_4469_ = (!crate::leanh::lean_is_exclusive(v___x_4460_)) as u8;
                    if v_isSharedCheck_4469_ == 0 {
                        v___x_4464_ = v___x_4460_;
                        v_isShared_4465_ = v_isSharedCheck_4469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4462_);
                        crate::leanh::lean_inc(v_a_4461_);
                        crate::leanh::lean_dec(v___x_4460_);
                        v___x_4464_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_a_4462_);
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
    mut v_x_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4473_ = l_Lean_Meta_Sym___aux__Lean__Meta__Sym__SymM______macroRules__Lean__Meta__Sym__doElemReportDbgIssue_x21______1(v_x_4470_, v_a_4471_, v_a_4472_);
    crate::leanh::lean_dec_ref(v_a_4471_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___redArg(
    mut v_a_4474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4476_ = lean_st_ref_get(v_a_4474_);
    v_issues_4477_ = crate::leanh::lean_ctor_get(v___x_4476_, 8);
    crate::leanh::lean_inc(v_issues_4477_);
    crate::leanh::lean_dec(v___x_4476_);
    v___x_4478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4478_, 0, v_issues_4477_);
    return v___x_4478_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___redArg___boxed(
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4479_);
    crate::leanh::lean_dec(v_a_4479_);
    return v_res_4481_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues(
    mut v_a_4482_: *mut crate::leanh::LeanObject,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
    mut v_a_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_a_4486_: *mut crate::leanh::LeanObject,
    mut v_a_4487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4489_ = l_Lean_Meta_Sym_getIssues___redArg(v_a_4483_);
    return v___x_4489_;
}
pub unsafe fn l_Lean_Meta_Sym_getIssues___boxed(
    mut v_a_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
    mut v_a_4495_: *mut crate::leanh::LeanObject,
    mut v_a_4496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4497_ = l_Lean_Meta_Sym_getIssues(
        v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_,
    );
    crate::leanh::lean_dec(v_a_4495_);
    crate::leanh::lean_dec_ref(v_a_4494_);
    crate::leanh::lean_dec(v_a_4493_);
    crate::leanh::lean_dec_ref(v_a_4492_);
    crate::leanh::lean_dec(v_a_4491_);
    crate::leanh::lean_dec_ref(v_a_4490_);
    return v_res_4497_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
    mut v_a_4498_: *mut crate::leanh::LeanObject,
    mut v_issues_4499_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4513_: u8 = 0;
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4502_ = lean_st_ref_take(v_a_4498_);
                v_share_4503_ = crate::leanh::lean_ctor_get(v___x_4502_, 0);
                v_maxFVar_4504_ = crate::leanh::lean_ctor_get(v___x_4502_, 1);
                v_proofInstInfo_4505_ = crate::leanh::lean_ctor_get(v___x_4502_, 2);
                v_inferType_4506_ = crate::leanh::lean_ctor_get(v___x_4502_, 3);
                v_getLevel_4507_ = crate::leanh::lean_ctor_get(v___x_4502_, 4);
                v_congrInfo_4508_ = crate::leanh::lean_ctor_get(v___x_4502_, 5);
                v_defEqI_4509_ = crate::leanh::lean_ctor_get(v___x_4502_, 6);
                v_extensions_4510_ = crate::leanh::lean_ctor_get(v___x_4502_, 7);
                v_issues_4511_ = crate::leanh::lean_ctor_get(v___x_4502_, 8);
                v_canon_4512_ = crate::leanh::lean_ctor_get(v___x_4502_, 9);
                v_debug_4513_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4502_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4524_ = (!crate::leanh::lean_is_exclusive(v___x_4502_)) as u8;
                if v_isSharedCheck_4524_ == 0 {
                    v___x_4515_ = v___x_4502_;
                    v_isShared_4516_ = v_isSharedCheck_4524_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4512_);
                    crate::leanh::lean_inc(v_issues_4511_);
                    crate::leanh::lean_inc(v_extensions_4510_);
                    crate::leanh::lean_inc(v_defEqI_4509_);
                    crate::leanh::lean_inc(v_congrInfo_4508_);
                    crate::leanh::lean_inc(v_getLevel_4507_);
                    crate::leanh::lean_inc(v_inferType_4506_);
                    crate::leanh::lean_inc(v_proofInstInfo_4505_);
                    crate::leanh::lean_inc(v_maxFVar_4504_);
                    crate::leanh::lean_inc(v_share_4503_);
                    crate::leanh::lean_dec(v___x_4502_);
                    v___x_4515_ = crate::leanh::lean_box(0);
                    v_isShared_4516_ = v_isSharedCheck_4524_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4517_ = l_List_appendTR___redArg(v_issues_4511_, v_issues_4499_);
                if v_isShared_4516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4515_, 8, v___x_4517_);
                    v___x_4519_ = v___x_4515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4523_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_share_4503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 1, v_maxFVar_4504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 2, v_proofInstInfo_4505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 3, v_inferType_4506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 4, v_getLevel_4507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 5, v_congrInfo_4508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 6, v_defEqI_4509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 7, v_extensions_4510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 8, v___x_4517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4523_, 9, v_canon_4512_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4523_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4513_,
                    );
                    v___x_4519_ = v_reuseFailAlloc_4523_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4520_ = lean_st_ref_set(v_a_4498_, v___x_4519_);
                v___x_4521_ = crate::leanh::lean_box(0);
                v___x_4522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4522_, 0, v___x_4521_);
                return v___x_4522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0___boxed(
    mut v_a_4525_: *mut crate::leanh::LeanObject,
    mut v_issues_4526_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4529_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
        v_a_4525_,
        v_issues_4526_,
        v_a_x3f_4527_,
    );
    crate::leanh::lean_dec(v_a_x3f_4527_);
    crate::leanh::lean_dec(v_a_4525_);
    return v_res_4529_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___redArg(
    mut v_x_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
    mut v_a_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4549_: u8 = 0;
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_unused_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4581_: u8 = 0;
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4585_: u8 = 0;
    let mut v_unused_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v_unused_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4538_ = lean_st_ref_get(v_a_4532_);
                v___x_4539_ = lean_st_ref_take(v_a_4532_);
                v_share_4540_ = crate::leanh::lean_ctor_get(v___x_4539_, 0);
                v_maxFVar_4541_ = crate::leanh::lean_ctor_get(v___x_4539_, 1);
                v_proofInstInfo_4542_ = crate::leanh::lean_ctor_get(v___x_4539_, 2);
                v_inferType_4543_ = crate::leanh::lean_ctor_get(v___x_4539_, 3);
                v_getLevel_4544_ = crate::leanh::lean_ctor_get(v___x_4539_, 4);
                v_congrInfo_4545_ = crate::leanh::lean_ctor_get(v___x_4539_, 5);
                v_defEqI_4546_ = crate::leanh::lean_ctor_get(v___x_4539_, 6);
                v_extensions_4547_ = crate::leanh::lean_ctor_get(v___x_4539_, 7);
                v_canon_4548_ = crate::leanh::lean_ctor_get(v___x_4539_, 9);
                v_debug_4549_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4539_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4588_ = (!crate::leanh::lean_is_exclusive(v___x_4539_)) as u8;
                if v_isSharedCheck_4588_ == 0 {
                    v_unused_4589_ = crate::leanh::lean_ctor_get(v___x_4539_, 8);
                    crate::leanh::lean_dec(v_unused_4589_);
                    v___x_4551_ = v___x_4539_;
                    v_isShared_4552_ = v_isSharedCheck_4588_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4548_);
                    crate::leanh::lean_inc(v_extensions_4547_);
                    crate::leanh::lean_inc(v_defEqI_4546_);
                    crate::leanh::lean_inc(v_congrInfo_4545_);
                    crate::leanh::lean_inc(v_getLevel_4544_);
                    crate::leanh::lean_inc(v_inferType_4543_);
                    crate::leanh::lean_inc(v_proofInstInfo_4542_);
                    crate::leanh::lean_inc(v_maxFVar_4541_);
                    crate::leanh::lean_inc(v_share_4540_);
                    crate::leanh::lean_dec(v___x_4539_);
                    v___x_4551_ = crate::leanh::lean_box(0);
                    v_isShared_4552_ = v_isSharedCheck_4588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4553_ = crate::leanh::lean_box(0);
                if v_isShared_4552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4551_, 8, v___x_4553_);
                    v___x_4555_ = v___x_4551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_share_4540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 1, v_maxFVar_4541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 2, v_proofInstInfo_4542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 3, v_inferType_4543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 4, v_getLevel_4544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 5, v_congrInfo_4545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 6, v_defEqI_4546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 7, v_extensions_4547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 8, v___x_4553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 9, v_canon_4548_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4587_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4549_,
                    );
                    v___x_4555_ = v_reuseFailAlloc_4587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4556_ = lean_st_ref_set(v_a_4532_, v___x_4555_);
                v_issues_4557_ = crate::leanh::lean_ctor_get(v___x_4538_, 8);
                crate::leanh::lean_inc(v_issues_4557_);
                crate::leanh::lean_dec(v___x_4538_);
                crate::leanh::lean_inc(v_a_4536_);
                crate::leanh::lean_inc_ref(v_a_4535_);
                crate::leanh::lean_inc(v_a_4534_);
                crate::leanh::lean_inc_ref(v_a_4533_);
                crate::leanh::lean_inc(v_a_4532_);
                crate::leanh::lean_inc_ref(v_a_4531_);
                v_r_4558_ = crate::leanh::lean_apply_7(
                    v_x_4530_,
                    v_a_4531_,
                    v_a_4532_,
                    v_a_4533_,
                    v_a_4534_,
                    v_a_4535_,
                    v_a_4536_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_4558_) == 0 {
                    v_a_4559_ = crate::leanh::lean_ctor_get(v_r_4558_, 0);
                    v_isSharedCheck_4575_ = (!crate::leanh::lean_is_exclusive(v_r_4558_)) as u8;
                    if v_isSharedCheck_4575_ == 0 {
                        v___x_4561_ = v_r_4558_;
                        v_isShared_4562_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4559_);
                        crate::leanh::lean_dec(v_r_4558_);
                        v___x_4561_ = crate::leanh::lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4576_ = crate::leanh::lean_ctor_get(v_r_4558_, 0);
                    crate::leanh::lean_inc(v_a_4576_);
                    crate::leanh::lean_dec_ref_known(v_r_4558_, 1);
                    v___x_4577_ = crate::leanh::lean_box(0);
                    v___x_4578_ = l_Lean_Meta_Sym_withNewIssueContext___redArg___lam__0(
                        v_a_4532_,
                        v_issues_4557_,
                        v___x_4577_,
                    );
                    v_isSharedCheck_4585_ = (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4585_ == 0 {
                        v_unused_4586_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                        crate::leanh::lean_dec(v_unused_4586_);
                        v___x_4580_ = v___x_4578_;
                        v_isShared_4581_ = v_isSharedCheck_4585_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4578_);
                        v___x_4580_ = crate::leanh::lean_box(0);
                        v_isShared_4581_ = v_isSharedCheck_4585_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_4559_);
                if v_isShared_4562_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4561_, 1);
                    v___x_4564_ = v___x_4561_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4559_);
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
                crate::leanh::lean_dec_ref(v___x_4564_);
                v_isSharedCheck_4572_ = (!crate::leanh::lean_is_exclusive(v___x_4565_)) as u8;
                if v_isSharedCheck_4572_ == 0 {
                    v_unused_4573_ = crate::leanh::lean_ctor_get(v___x_4565_, 0);
                    crate::leanh::lean_dec(v_unused_4573_);
                    v___x_4567_ = v___x_4565_;
                    v_isShared_4568_ = v_isSharedCheck_4572_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4565_);
                    v___x_4567_ = crate::leanh::lean_box(0);
                    v_isShared_4568_ = v_isSharedCheck_4572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4567_, 0, v_a_4559_);
                    v___x_4570_ = v___x_4567_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4559_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_4580_, 1);
                    crate::leanh::lean_ctor_set(v___x_4580_, 0, v_a_4576_);
                    v___x_4583_ = v___x_4580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4576_);
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
    mut v_x_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4598_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(
        v_x_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_,
    );
    crate::leanh::lean_dec(v_a_4596_);
    crate::leanh::lean_dec_ref(v_a_4595_);
    crate::leanh::lean_dec(v_a_4594_);
    crate::leanh::lean_dec_ref(v_a_4593_);
    crate::leanh::lean_dec(v_a_4592_);
    crate::leanh::lean_dec_ref(v_a_4591_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext(
    mut v_00_u03b1_4599_: *mut crate::leanh::LeanObject,
    mut v_x_4600_: *mut crate::leanh::LeanObject,
    mut v_a_4601_: *mut crate::leanh::LeanObject,
    mut v_a_4602_: *mut crate::leanh::LeanObject,
    mut v_a_4603_: *mut crate::leanh::LeanObject,
    mut v_a_4604_: *mut crate::leanh::LeanObject,
    mut v_a_4605_: *mut crate::leanh::LeanObject,
    mut v_a_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ = l_Lean_Meta_Sym_withNewIssueContext___redArg(
        v_x_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_,
    );
    return v___x_4608_;
}
pub unsafe fn l_Lean_Meta_Sym_withNewIssueContext___boxed(
    mut v_00_u03b1_4609_: *mut crate::leanh::LeanObject,
    mut v_x_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_4616_);
    crate::leanh::lean_dec_ref(v_a_4615_);
    crate::leanh::lean_dec(v_a_4614_);
    crate::leanh::lean_dec_ref(v_a_4613_);
    crate::leanh::lean_dec(v_a_4612_);
    crate::leanh::lean_dec_ref(v_a_4611_);
    return v_res_4618_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4619_: *mut crate::leanh::LeanObject,
    mut v_vals_4620_: *mut crate::leanh::LeanObject,
    mut v_i_4621_: *mut crate::leanh::LeanObject,
    mut v_k_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4624_: u8 = 0;
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: u8 = 0;
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: u8 = 0;
    let mut v___x_4639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4630_ = lean_array_get_size(v_keys_4619_);
                v___x_4631_ = lean_nat_dec_lt(v_i_4621_, v___x_4630_);
                if v___x_4631_ == 0 {
                    crate::leanh::lean_dec(v_i_4621_);
                    v___x_4632_ = crate::leanh::lean_box(0);
                    return v___x_4632_;
                } else {
                    v_fst_4633_ = crate::leanh::lean_ctor_get(v_k_4622_, 0);
                    v_snd_4634_ = crate::leanh::lean_ctor_get(v_k_4622_, 1);
                    v_k_x27_4635_ = lean_array_fget_borrowed(v_keys_4619_, v_i_4621_);
                    v_fst_4636_ = crate::leanh::lean_ctor_get(v_k_x27_4635_, 0);
                    v_snd_4637_ = crate::leanh::lean_ctor_get(v_k_x27_4635_, 1);
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
                    v___x_4625_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4626_ = lean_nat_add(v_i_4621_, v___x_4625_);
                    crate::leanh::lean_dec(v_i_4621_);
                    v_i_4621_ = v___x_4626_;
                    state = 0;
                    continue;
                } else {
                    v___x_4628_ = lean_array_fget_borrowed(v_vals_4620_, v_i_4621_);
                    crate::leanh::lean_dec(v_i_4621_);
                    crate::leanh::lean_inc(v___x_4628_);
                    v___x_4629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
                    return v___x_4629_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4640_: *mut crate::leanh::LeanObject,
    mut v_vals_4641_: *mut crate::leanh::LeanObject,
    mut v_i_4642_: *mut crate::leanh::LeanObject,
    mut v_k_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4640_, v_vals_4641_, v_i_4642_, v_k_4643_);
    crate::leanh::lean_dec_ref(v_k_4643_);
    crate::leanh::lean_dec_ref(v_vals_4641_);
    crate::leanh::lean_dec_ref(v_keys_4640_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(
    mut v_x_4645_: *mut crate::leanh::LeanObject,
    mut v_x_4646_: usize,
    mut v_x_4647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: usize = 0;
    let mut v___x_4651_: usize = 0;
    let mut v___x_4652_: usize = 0;
    let mut v_j_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4658_: u8 = 0;
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: u8 = 0;
    let mut v___x_4666_: u8 = 0;
    let mut v_node_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: usize = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4645_) == 0 {
                    v_es_4648_ = crate::leanh::lean_ctor_get(v_x_4645_, 0);
                    v___x_4649_ = crate::leanh::lean_box(2);
                    v___x_4650_ = 5usize;
                    v___x_4651_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_4652_ = lean_usize_land(v_x_4646_, v___x_4651_);
                    v_j_4653_ = lean_usize_to_nat(v___x_4652_);
                    v___x_4654_ = lean_array_get_borrowed(v___x_4649_, v_es_4648_, v_j_4653_);
                    crate::leanh::lean_dec(v_j_4653_);
                    match crate::leanh::lean_obj_tag(v___x_4654_) {
                        0 => {
                            v_key_4655_ = crate::leanh::lean_ctor_get(v___x_4654_, 0);
                            v_val_4656_ = crate::leanh::lean_ctor_get(v___x_4654_, 1);
                            v_fst_4661_ = crate::leanh::lean_ctor_get(v_x_4647_, 0);
                            v_snd_4662_ = crate::leanh::lean_ctor_get(v_x_4647_, 1);
                            v_fst_4663_ = crate::leanh::lean_ctor_get(v_key_4655_, 0);
                            v_snd_4664_ = crate::leanh::lean_ctor_get(v_key_4655_, 1);
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
                            v_node_4667_ = crate::leanh::lean_ctor_get(v___x_4654_, 0);
                            v___x_4668_ = lean_usize_shift_right(v_x_4646_, v___x_4650_);
                            v_x_4645_ = v_node_4667_;
                            v_x_4646_ = v___x_4668_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4670_ = crate::leanh::lean_box(0);
                            return v___x_4670_;
                        }
                    }
                } else {
                    v_ks_4671_ = crate::leanh::lean_ctor_get(v_x_4645_, 0);
                    v_vs_4672_ = crate::leanh::lean_ctor_get(v_x_4645_, 1);
                    v___x_4673_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4674_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_ks_4671_, v_vs_4672_, v___x_4673_, v_x_4647_);
                    return v___x_4674_;
                }
            }
            1 => {
                if v___y_4658_ == 0 {
                    v___x_4659_ = crate::leanh::lean_box(0);
                    return v___x_4659_;
                } else {
                    crate::leanh::lean_inc(v_val_4656_);
                    v___x_4660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4660_, 0, v_val_4656_);
                    return v___x_4660_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg___boxed(
    mut v_x_4675_: *mut crate::leanh::LeanObject,
    mut v_x_4676_: *mut crate::leanh::LeanObject,
    mut v_x_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2658__boxed_4678_: usize = 0;
    let mut v_res_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2658__boxed_4678_ = crate::leanh::lean_unbox_usize(v_x_4676_);
    crate::leanh::lean_dec(v_x_4676_);
    v_res_4679_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4675_, v_x_2658__boxed_4678_, v_x_4677_);
    crate::leanh::lean_dec_ref(v_x_4677_);
    crate::leanh::lean_dec_ref(v_x_4675_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
    mut v_x_4680_: *mut crate::leanh::LeanObject,
    mut v_x_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u64 = 0;
    let mut v___x_4685_: u64 = 0;
    let mut v___x_4686_: u64 = 0;
    let mut v___x_4687_: usize = 0;
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4682_ = crate::leanh::lean_ctor_get(v_x_4681_, 0);
    v_snd_4683_ = crate::leanh::lean_ctor_get(v_x_4681_, 1);
    v___x_4684_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4682_);
    v___x_4685_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4683_);
    v___x_4686_ = lean_uint64_mix_hash(v___x_4684_, v___x_4685_);
    v___x_4687_ = lean_uint64_to_usize(v___x_4686_);
    v___x_4688_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4680_, v___x_4687_, v_x_4681_);
    return v___x_4688_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg___boxed(
    mut v_x_4689_: *mut crate::leanh::LeanObject,
    mut v_x_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
            v_x_4689_, v_x_4690_,
        );
    crate::leanh::lean_dec_ref(v_x_4690_);
    crate::leanh::lean_dec_ref(v_x_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_4692_: *mut crate::leanh::LeanObject,
    mut v_x_4693_: *mut crate::leanh::LeanObject,
    mut v_x_4694_: *mut crate::leanh::LeanObject,
    mut v_x_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v___y_4702_: u8 = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: u8 = 0;
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4696_ = crate::leanh::lean_ctor_get(v_x_4692_, 0);
                v_vs_4697_ = crate::leanh::lean_ctor_get(v_x_4692_, 1);
                v_isSharedCheck_4726_ = (!crate::leanh::lean_is_exclusive(v_x_4692_)) as u8;
                if v_isSharedCheck_4726_ == 0 {
                    v___x_4699_ = v_x_4692_;
                    v_isShared_4700_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4697_);
                    crate::leanh::lean_inc(v_ks_4696_);
                    crate::leanh::lean_dec(v_x_4692_);
                    v___x_4699_ = crate::leanh::lean_box(0);
                    v_isShared_4700_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4714_ = lean_array_get_size(v_ks_4696_);
                v___x_4715_ = lean_nat_dec_lt(v_x_4693_, v___x_4714_);
                if v___x_4715_ == 0 {
                    crate::leanh::lean_del_object(v___x_4699_);
                    crate::leanh::lean_dec(v_x_4693_);
                    v___x_4716_ = lean_array_push(v_ks_4696_, v_x_4694_);
                    v___x_4717_ = lean_array_push(v_vs_4697_, v_x_4695_);
                    v___x_4718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4718_, 0, v___x_4716_);
                    crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
                    return v___x_4718_;
                } else {
                    v_fst_4719_ = crate::leanh::lean_ctor_get(v_x_4694_, 0);
                    v_snd_4720_ = crate::leanh::lean_ctor_get(v_x_4694_, 1);
                    v_k_x27_4721_ = lean_array_fget_borrowed(v_ks_4696_, v_x_4693_);
                    v_fst_4722_ = crate::leanh::lean_ctor_get(v_k_x27_4721_, 0);
                    v_snd_4723_ = crate::leanh::lean_ctor_get(v_k_x27_4721_, 1);
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
                        v_reuseFailAlloc_4708_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_ks_4696_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_vs_4697_);
                        v___x_4704_ = v_reuseFailAlloc_4708_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4709_ = lean_array_fset(v_ks_4696_, v_x_4693_, v_x_4694_);
                    v___x_4710_ = lean_array_fset(v_vs_4697_, v_x_4693_, v_x_4695_);
                    crate::leanh::lean_dec(v_x_4693_);
                    if v_isShared_4700_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4699_, 1, v___x_4710_);
                        crate::leanh::lean_ctor_set(v___x_4699_, 0, v___x_4709_);
                        v___x_4712_ = v___x_4699_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4709_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 1, v___x_4710_);
                        v___x_4712_ = v_reuseFailAlloc_4713_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4705_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4706_ = lean_nat_add(v_x_4693_, v___x_4705_);
                crate::leanh::lean_dec(v_x_4693_);
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
    mut v_n_4727_: *mut crate::leanh::LeanObject,
    mut v_k_4728_: *mut crate::leanh::LeanObject,
    mut v_v_4729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4731_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_n_4727_, v___x_4730_, v_k_4728_, v_v_4729_);
    return v___x_4731_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4732_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(
    mut v_x_4733_: *mut crate::leanh::LeanObject,
    mut v_x_4734_: usize,
    mut v_x_4735_: usize,
    mut v_x_4736_: *mut crate::leanh::LeanObject,
    mut v_x_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: usize = 0;
    let mut v___x_4740_: usize = 0;
    let mut v___x_4741_: usize = 0;
    let mut v___x_4742_: usize = 0;
    let mut v_j_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: u8 = 0;
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v_v_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4762_: u8 = 0;
    let mut v___y_4764_: u8 = 0;
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: u8 = 0;
    let mut v_isSharedCheck_4776_: u8 = 0;
    let mut v_node_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4780_: u8 = 0;
    let mut v___x_4781_: usize = 0;
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4789_: u8 = 0;
    let mut v_unused_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4795_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: u8 = 0;
    let mut v_ks_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: usize = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v_reuseFailAlloc_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4733_) == 0 {
                    v_es_4738_ = crate::leanh::lean_ctor_get(v_x_4733_, 0);
                    v___x_4739_ = 5usize;
                    v___x_4740_ = 1usize;
                    v___x_4741_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Sym_shareCommon_spec__0_spec__0___redArg___closed__1);
                    v___x_4742_ = lean_usize_land(v_x_4734_, v___x_4741_);
                    v_j_4743_ = lean_usize_to_nat(v___x_4742_);
                    v___x_4744_ = lean_array_get_size(v_es_4738_);
                    v___x_4745_ = lean_nat_dec_lt(v_j_4743_, v___x_4744_);
                    if v___x_4745_ == 0 {
                        crate::leanh::lean_dec(v_j_4743_);
                        crate::leanh::lean_dec(v_x_4737_);
                        crate::leanh::lean_dec_ref(v_x_4736_);
                        return v_x_4733_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4738_);
                        v_isSharedCheck_4789_ = (!crate::leanh::lean_is_exclusive(v_x_4733_)) as u8;
                        if v_isSharedCheck_4789_ == 0 {
                            v_unused_4790_ = crate::leanh::lean_ctor_get(v_x_4733_, 0);
                            crate::leanh::lean_dec(v_unused_4790_);
                            v___x_4747_ = v_x_4733_;
                            v_isShared_4748_ = v_isSharedCheck_4789_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4733_);
                            v___x_4747_ = crate::leanh::lean_box(0);
                            v_isShared_4748_ = v_isSharedCheck_4789_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4791_ = crate::leanh::lean_ctor_get(v_x_4733_, 0);
                    v_vs_4792_ = crate::leanh::lean_ctor_get(v_x_4733_, 1);
                    v_isSharedCheck_4812_ = (!crate::leanh::lean_is_exclusive(v_x_4733_)) as u8;
                    if v_isSharedCheck_4812_ == 0 {
                        v___x_4794_ = v_x_4733_;
                        v_isShared_4795_ = v_isSharedCheck_4812_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4792_);
                        crate::leanh::lean_inc(v_ks_4791_);
                        crate::leanh::lean_dec(v_x_4733_);
                        v___x_4794_ = crate::leanh::lean_box(0);
                        v_isShared_4795_ = v_isSharedCheck_4812_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4749_ = lean_array_fget(v_es_4738_, v_j_4743_);
                v___x_4750_ = crate::leanh::lean_box(0);
                v_xs_x27_4751_ = lean_array_fset(v_es_4738_, v_j_4743_, v___x_4750_);
                match crate::leanh::lean_obj_tag(v_v_4749_) {
                    0 => {
                        v_key_4758_ = crate::leanh::lean_ctor_get(v_v_4749_, 0);
                        v_val_4759_ = crate::leanh::lean_ctor_get(v_v_4749_, 1);
                        v_isSharedCheck_4776_ = (!crate::leanh::lean_is_exclusive(v_v_4749_)) as u8;
                        if v_isSharedCheck_4776_ == 0 {
                            v___x_4761_ = v_v_4749_;
                            v_isShared_4762_ = v_isSharedCheck_4776_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4759_);
                            crate::leanh::lean_inc(v_key_4758_);
                            crate::leanh::lean_dec(v_v_4749_);
                            v___x_4761_ = crate::leanh::lean_box(0);
                            v_isShared_4762_ = v_isSharedCheck_4776_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4777_ = crate::leanh::lean_ctor_get(v_v_4749_, 0);
                        v_isSharedCheck_4787_ = (!crate::leanh::lean_is_exclusive(v_v_4749_)) as u8;
                        if v_isSharedCheck_4787_ == 0 {
                            v___x_4779_ = v_v_4749_;
                            v_isShared_4780_ = v_isSharedCheck_4787_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4777_);
                            crate::leanh::lean_dec(v_v_4749_);
                            v___x_4779_ = crate::leanh::lean_box(0);
                            v_isShared_4780_ = v_isSharedCheck_4787_;
                            state = 7;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4788_, 0, v_x_4736_);
                        crate::leanh::lean_ctor_set(v___x_4788_, 1, v_x_4737_);
                        v___y_4753_ = v___x_4788_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4754_ = lean_array_fset(v_xs_x27_4751_, v_j_4743_, v___y_4753_);
                crate::leanh::lean_dec(v_j_4743_);
                if v_isShared_4748_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4747_, 0, v___x_4754_);
                    v___x_4756_ = v___x_4747_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
                    v___x_4756_ = v_reuseFailAlloc_4757_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4756_;
            }
            4 => {
                v_fst_4770_ = crate::leanh::lean_ctor_get(v_x_4736_, 0);
                v_snd_4771_ = crate::leanh::lean_ctor_get(v_x_4736_, 1);
                v_fst_4772_ = crate::leanh::lean_ctor_get(v_key_4758_, 0);
                v_snd_4773_ = crate::leanh::lean_ctor_get(v_key_4758_, 1);
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
                    crate::leanh::lean_del_object(v___x_4761_);
                    v___x_4765_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4758_,
                        v_val_4759_,
                        v_x_4736_,
                        v_x_4737_,
                    );
                    v___x_4766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4766_, 0, v___x_4765_);
                    v___y_4753_ = v___x_4766_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4759_);
                    crate::leanh::lean_dec(v_key_4758_);
                    if v_isShared_4762_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4761_, 1, v_x_4737_);
                        crate::leanh::lean_ctor_set(v___x_4761_, 0, v_x_4736_);
                        v___x_4768_ = v___x_4761_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4769_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_x_4736_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 1, v_x_4737_);
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
                    crate::leanh::lean_ctor_set(v___x_4779_, 0, v___x_4783_);
                    v___x_4785_ = v___x_4779_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
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
                    v_reuseFailAlloc_4811_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_ks_4791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_vs_4792_);
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
                    v___x_4809_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4810_ = lean_nat_dec_lt(v___x_4808_, v___x_4809_);
                    crate::leanh::lean_dec(v___x_4808_);
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
                    v_ks_4801_ = crate::leanh::lean_ctor_get(v_newNode_4798_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4801_);
                    v_vs_4802_ = crate::leanh::lean_ctor_get(v_newNode_4798_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4802_);
                    crate::leanh::lean_dec_ref(v_newNode_4798_);
                    v___x_4803_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___closed__0);
                    v___x_4805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_x_4735_, v_ks_4801_, v_vs_4802_, v___x_4803_, v___x_4804_);
                    crate::leanh::lean_dec_ref(v_vs_4802_);
                    crate::leanh::lean_dec_ref(v_ks_4801_);
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
    mut v_keys_4814_: *mut crate::leanh::LeanObject,
    mut v_vals_4815_: *mut crate::leanh::LeanObject,
    mut v_i_4816_: *mut crate::leanh::LeanObject,
    mut v_entries_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: u8 = 0;
    let mut v_k_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u64 = 0;
    let mut v___x_4825_: u64 = 0;
    let mut v___x_4826_: u64 = 0;
    let mut v_h_4827_: usize = 0;
    let mut v___x_4828_: usize = 0;
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: usize = 0;
    let mut v___x_4831_: usize = 0;
    let mut v___x_4832_: usize = 0;
    let mut v_h_4833_: usize = 0;
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4818_ = lean_array_get_size(v_keys_4814_);
                v___x_4819_ = lean_nat_dec_lt(v_i_4816_, v___x_4818_);
                if v___x_4819_ == 0 {
                    crate::leanh::lean_dec(v_i_4816_);
                    return v_entries_4817_;
                } else {
                    v_k_4820_ = lean_array_fget_borrowed(v_keys_4814_, v_i_4816_);
                    v_fst_4821_ = crate::leanh::lean_ctor_get(v_k_4820_, 0);
                    v_snd_4822_ = crate::leanh::lean_ctor_get(v_k_4820_, 1);
                    v_v_4823_ = lean_array_fget_borrowed(v_vals_4815_, v_i_4816_);
                    v___x_4824_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4821_);
                    v___x_4825_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4822_);
                    v___x_4826_ = lean_uint64_mix_hash(v___x_4824_, v___x_4825_);
                    v_h_4827_ = lean_uint64_to_usize(v___x_4826_);
                    v___x_4828_ = 5usize;
                    v___x_4829_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4830_ = 1usize;
                    v___x_4831_ = lean_usize_sub(v_depth_4813_, v___x_4830_);
                    v___x_4832_ = lean_usize_mul(v___x_4828_, v___x_4831_);
                    v_h_4833_ = lean_usize_shift_right(v_h_4827_, v___x_4832_);
                    v___x_4834_ = lean_nat_add(v_i_4816_, v___x_4829_);
                    crate::leanh::lean_dec(v_i_4816_);
                    crate::leanh::lean_inc(v_v_4823_);
                    crate::leanh::lean_inc(v_k_4820_);
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
    mut v_depth_4837_: *mut crate::leanh::LeanObject,
    mut v_keys_4838_: *mut crate::leanh::LeanObject,
    mut v_vals_4839_: *mut crate::leanh::LeanObject,
    mut v_i_4840_: *mut crate::leanh::LeanObject,
    mut v_entries_4841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4842_: usize = 0;
    let mut v_res_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4842_ = crate::leanh::lean_unbox_usize(v_depth_4837_);
    crate::leanh::lean_dec(v_depth_4837_);
    v_res_4843_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_boxed_4842_, v_keys_4838_, v_vals_4839_, v_i_4840_, v_entries_4841_);
    crate::leanh::lean_dec_ref(v_vals_4839_);
    crate::leanh::lean_dec_ref(v_keys_4838_);
    return v_res_4843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg___boxed(
    mut v_x_4844_: *mut crate::leanh::LeanObject,
    mut v_x_4845_: *mut crate::leanh::LeanObject,
    mut v_x_4846_: *mut crate::leanh::LeanObject,
    mut v_x_4847_: *mut crate::leanh::LeanObject,
    mut v_x_4848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2837__boxed_4849_: usize = 0;
    let mut v_x_2838__boxed_4850_: usize = 0;
    let mut v_res_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2837__boxed_4849_ = crate::leanh::lean_unbox_usize(v_x_4845_);
    crate::leanh::lean_dec(v_x_4845_);
    v_x_2838__boxed_4850_ = crate::leanh::lean_unbox_usize(v_x_4846_);
    crate::leanh::lean_dec(v_x_4846_);
    v_res_4851_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4844_, v_x_2837__boxed_4849_, v_x_2838__boxed_4850_, v_x_4847_, v_x_4848_);
    return v_res_4851_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(
    mut v_x_4852_: *mut crate::leanh::LeanObject,
    mut v_x_4853_: *mut crate::leanh::LeanObject,
    mut v_x_4854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: u64 = 0;
    let mut v___x_4858_: u64 = 0;
    let mut v___x_4859_: u64 = 0;
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: usize = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4855_ = crate::leanh::lean_ctor_get(v_x_4853_, 0);
    v_snd_4856_ = crate::leanh::lean_ctor_get(v_x_4853_, 1);
    v___x_4857_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_4855_);
    v___x_4858_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_snd_4856_);
    v___x_4859_ = lean_uint64_mix_hash(v___x_4857_, v___x_4858_);
    v___x_4860_ = lean_uint64_to_usize(v___x_4859_);
    v___x_4861_ = 1usize;
    v___x_4862_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4852_, v___x_4860_, v___x_4861_, v_x_4853_, v_x_4854_);
    return v___x_4862_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI___redArg(
    mut v_s_4863_: *mut crate::leanh::LeanObject,
    mut v_t_4864_: *mut crate::leanh::LeanObject,
    mut v_a_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4878_: u8 = 0;
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4882_: u8 = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4887_: u8 = 0;
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4899_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4871_ = lean_st_ref_get(v_a_4865_);
                v_defEqI_4872_ = crate::leanh::lean_ctor_get(v___x_4871_, 6);
                crate::leanh::lean_inc_ref(v_defEqI_4872_);
                crate::leanh::lean_dec(v___x_4871_);
                crate::leanh::lean_inc_ref(v_t_4864_);
                crate::leanh::lean_inc_ref(v_s_4863_);
                v_key_4873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_key_4873_, 0, v_s_4863_);
                crate::leanh::lean_ctor_set(v_key_4873_, 1, v_t_4864_);
                v___x_4874_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(v_defEqI_4872_, v_key_4873_);
                crate::leanh::lean_dec_ref(v_defEqI_4872_);
                if crate::leanh::lean_obj_tag(v___x_4874_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_key_4873_, 2);
                    crate::leanh::lean_dec_ref(v_t_4864_);
                    crate::leanh::lean_dec_ref(v_s_4863_);
                    v_val_4875_ = crate::leanh::lean_ctor_get(v___x_4874_, 0);
                    v_isSharedCheck_4882_ = (!crate::leanh::lean_is_exclusive(v___x_4874_)) as u8;
                    if v_isSharedCheck_4882_ == 0 {
                        v___x_4877_ = v___x_4874_;
                        v_isShared_4878_ = v_isSharedCheck_4882_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4875_);
                        crate::leanh::lean_dec(v___x_4874_);
                        v___x_4877_ = crate::leanh::lean_box(0);
                        v_isShared_4878_ = v_isSharedCheck_4882_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4874_);
                    v___x_4883_ = l_Lean_Meta_isDefEqI(
                        v_s_4863_, v_t_4864_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4883_) == 0 {
                        v_a_4884_ = crate::leanh::lean_ctor_get(v___x_4883_, 0);
                        v_isSharedCheck_4912_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4883_)) as u8;
                        if v_isSharedCheck_4912_ == 0 {
                            v___x_4886_ = v___x_4883_;
                            v_isShared_4887_ = v_isSharedCheck_4912_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4884_);
                            crate::leanh::lean_dec(v___x_4883_);
                            v___x_4886_ = crate::leanh::lean_box(0);
                            v_isShared_4887_ = v_isSharedCheck_4912_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_key_4873_, 2);
                        return v___x_4883_;
                    }
                }
            }
            1 => {
                if v_isShared_4878_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4877_, 0);
                    v___x_4880_ = v___x_4877_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_val_4875_);
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
                v_share_4889_ = crate::leanh::lean_ctor_get(v___x_4888_, 0);
                v_maxFVar_4890_ = crate::leanh::lean_ctor_get(v___x_4888_, 1);
                v_proofInstInfo_4891_ = crate::leanh::lean_ctor_get(v___x_4888_, 2);
                v_inferType_4892_ = crate::leanh::lean_ctor_get(v___x_4888_, 3);
                v_getLevel_4893_ = crate::leanh::lean_ctor_get(v___x_4888_, 4);
                v_congrInfo_4894_ = crate::leanh::lean_ctor_get(v___x_4888_, 5);
                v_defEqI_4895_ = crate::leanh::lean_ctor_get(v___x_4888_, 6);
                v_extensions_4896_ = crate::leanh::lean_ctor_get(v___x_4888_, 7);
                v_issues_4897_ = crate::leanh::lean_ctor_get(v___x_4888_, 8);
                v_canon_4898_ = crate::leanh::lean_ctor_get(v___x_4888_, 9);
                v_debug_4899_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4888_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4911_ = (!crate::leanh::lean_is_exclusive(v___x_4888_)) as u8;
                if v_isSharedCheck_4911_ == 0 {
                    v___x_4901_ = v___x_4888_;
                    v_isShared_4902_ = v_isSharedCheck_4911_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4898_);
                    crate::leanh::lean_inc(v_issues_4897_);
                    crate::leanh::lean_inc(v_extensions_4896_);
                    crate::leanh::lean_inc(v_defEqI_4895_);
                    crate::leanh::lean_inc(v_congrInfo_4894_);
                    crate::leanh::lean_inc(v_getLevel_4893_);
                    crate::leanh::lean_inc(v_inferType_4892_);
                    crate::leanh::lean_inc(v_proofInstInfo_4891_);
                    crate::leanh::lean_inc(v_maxFVar_4890_);
                    crate::leanh::lean_inc(v_share_4889_);
                    crate::leanh::lean_dec(v___x_4888_);
                    v___x_4901_ = crate::leanh::lean_box(0);
                    v_isShared_4902_ = v_isSharedCheck_4911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_4884_);
                v___x_4903_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(v_defEqI_4895_, v_key_4873_, v_a_4884_);
                if v_isShared_4902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4901_, 6, v___x_4903_);
                    v___x_4905_ = v___x_4901_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_share_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_maxFVar_4890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_proofInstInfo_4891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_inferType_4892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 4, v_getLevel_4893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 5, v_congrInfo_4894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 6, v___x_4903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 7, v_extensions_4896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 8, v_issues_4897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 9, v_canon_4898_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4910_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
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
                    v_reuseFailAlloc_4909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4884_);
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
    mut v_s_4913_: *mut crate::leanh::LeanObject,
    mut v_t_4914_: *mut crate::leanh::LeanObject,
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_a_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4921_ = l_Lean_Meta_Sym_isDefEqI___redArg(
        v_s_4913_, v_t_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_,
    );
    crate::leanh::lean_dec(v_a_4919_);
    crate::leanh::lean_dec_ref(v_a_4918_);
    crate::leanh::lean_dec(v_a_4917_);
    crate::leanh::lean_dec_ref(v_a_4916_);
    crate::leanh::lean_dec(v_a_4915_);
    return v_res_4921_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI(
    mut v_s_4922_: *mut crate::leanh::LeanObject,
    mut v_t_4923_: *mut crate::leanh::LeanObject,
    mut v_a_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4931_ = l_Lean_Meta_Sym_isDefEqI___redArg(
        v_s_4922_, v_t_4923_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_,
    );
    return v___x_4931_;
}
pub unsafe fn l_Lean_Meta_Sym_isDefEqI___boxed(
    mut v_s_4932_: *mut crate::leanh::LeanObject,
    mut v_t_4933_: *mut crate::leanh::LeanObject,
    mut v_a_4934_: *mut crate::leanh::LeanObject,
    mut v_a_4935_: *mut crate::leanh::LeanObject,
    mut v_a_4936_: *mut crate::leanh::LeanObject,
    mut v_a_4937_: *mut crate::leanh::LeanObject,
    mut v_a_4938_: *mut crate::leanh::LeanObject,
    mut v_a_4939_: *mut crate::leanh::LeanObject,
    mut v_a_4940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4941_ = l_Lean_Meta_Sym_isDefEqI(
        v_s_4932_, v_t_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_,
    );
    crate::leanh::lean_dec(v_a_4939_);
    crate::leanh::lean_dec_ref(v_a_4938_);
    crate::leanh::lean_dec(v_a_4937_);
    crate::leanh::lean_dec_ref(v_a_4936_);
    crate::leanh::lean_dec(v_a_4935_);
    crate::leanh::lean_dec_ref(v_a_4934_);
    return v_res_4941_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(
    mut v_00_u03b2_4942_: *mut crate::leanh::LeanObject,
    mut v_x_4943_: *mut crate::leanh::LeanObject,
    mut v_x_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4945_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___redArg(
            v_x_4943_, v_x_4944_,
        );
    return v___x_4945_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0___boxed(
    mut v_00_u03b2_4946_: *mut crate::leanh::LeanObject,
    mut v_x_4947_: *mut crate::leanh::LeanObject,
    mut v_x_4948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4949_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0(
        v_00_u03b2_4946_,
        v_x_4947_,
        v_x_4948_,
    );
    crate::leanh::lean_dec_ref(v_x_4948_);
    crate::leanh::lean_dec_ref(v_x_4947_);
    return v_res_4949_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1(
    mut v_00_u03b2_4950_: *mut crate::leanh::LeanObject,
    mut v_x_4951_: *mut crate::leanh::LeanObject,
    mut v_x_4952_: *mut crate::leanh::LeanObject,
    mut v_x_4953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1___redArg(
        v_x_4951_, v_x_4952_, v_x_4953_,
    );
    return v___x_4954_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(
    mut v_00_u03b2_4955_: *mut crate::leanh::LeanObject,
    mut v_x_4956_: *mut crate::leanh::LeanObject,
    mut v_x_4957_: usize,
    mut v_x_4958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4959_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___redArg(v_x_4956_, v_x_4957_, v_x_4958_);
    return v___x_4959_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0___boxed(
    mut v_00_u03b2_4960_: *mut crate::leanh::LeanObject,
    mut v_x_4961_: *mut crate::leanh::LeanObject,
    mut v_x_4962_: *mut crate::leanh::LeanObject,
    mut v_x_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3116__boxed_4964_: usize = 0;
    let mut v_res_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3116__boxed_4964_ = crate::leanh::lean_unbox_usize(v_x_4962_);
    crate::leanh::lean_dec(v_x_4962_);
    v_res_4965_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0(v_00_u03b2_4960_, v_x_4961_, v_x_3116__boxed_4964_, v_x_4963_);
    crate::leanh::lean_dec_ref(v_x_4963_);
    crate::leanh::lean_dec_ref(v_x_4961_);
    return v_res_4965_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(
    mut v_00_u03b2_4966_: *mut crate::leanh::LeanObject,
    mut v_x_4967_: *mut crate::leanh::LeanObject,
    mut v_x_4968_: usize,
    mut v_x_4969_: usize,
    mut v_x_4970_: *mut crate::leanh::LeanObject,
    mut v_x_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___redArg(v_x_4967_, v_x_4968_, v_x_4969_, v_x_4970_, v_x_4971_);
    return v___x_4972_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2___boxed(
    mut v_00_u03b2_4973_: *mut crate::leanh::LeanObject,
    mut v_x_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
    mut v_x_4976_: *mut crate::leanh::LeanObject,
    mut v_x_4977_: *mut crate::leanh::LeanObject,
    mut v_x_4978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3127__boxed_4979_: usize = 0;
    let mut v_x_3128__boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3127__boxed_4979_ = crate::leanh::lean_unbox_usize(v_x_4975_);
    crate::leanh::lean_dec(v_x_4975_);
    v_x_3128__boxed_4980_ = crate::leanh::lean_unbox_usize(v_x_4976_);
    crate::leanh::lean_dec(v_x_4976_);
    v_res_4981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2(v_00_u03b2_4973_, v_x_4974_, v_x_3127__boxed_4979_, v_x_3128__boxed_4980_, v_x_4977_, v_x_4978_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4982_: *mut crate::leanh::LeanObject,
    mut v_keys_4983_: *mut crate::leanh::LeanObject,
    mut v_vals_4984_: *mut crate::leanh::LeanObject,
    mut v_heq_4985_: *mut crate::leanh::LeanObject,
    mut v_i_4986_: *mut crate::leanh::LeanObject,
    mut v_k_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4988_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___redArg(v_keys_4983_, v_vals_4984_, v_i_4986_, v_k_4987_);
    return v___x_4988_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4989_: *mut crate::leanh::LeanObject,
    mut v_keys_4990_: *mut crate::leanh::LeanObject,
    mut v_vals_4991_: *mut crate::leanh::LeanObject,
    mut v_heq_4992_: *mut crate::leanh::LeanObject,
    mut v_i_4993_: *mut crate::leanh::LeanObject,
    mut v_k_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4995_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_isDefEqI_spec__0_spec__0_spec__1(v_00_u03b2_4989_, v_keys_4990_, v_vals_4991_, v_heq_4992_, v_i_4993_, v_k_4994_);
    crate::leanh::lean_dec_ref(v_k_4994_);
    crate::leanh::lean_dec_ref(v_vals_4991_);
    crate::leanh::lean_dec_ref(v_keys_4990_);
    return v_res_4995_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4996_: *mut crate::leanh::LeanObject,
    mut v_n_4997_: *mut crate::leanh::LeanObject,
    mut v_k_4998_: *mut crate::leanh::LeanObject,
    mut v_v_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5000_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4___redArg(v_n_4997_, v_k_4998_, v_v_4999_);
    return v___x_5000_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5001_: *mut crate::leanh::LeanObject,
    mut v_depth_5002_: usize,
    mut v_keys_5003_: *mut crate::leanh::LeanObject,
    mut v_vals_5004_: *mut crate::leanh::LeanObject,
    mut v_heq_5005_: *mut crate::leanh::LeanObject,
    mut v_i_5006_: *mut crate::leanh::LeanObject,
    mut v_entries_5007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5008_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___redArg(v_depth_5002_, v_keys_5003_, v_vals_5004_, v_i_5006_, v_entries_5007_);
    return v___x_5008_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_5009_: *mut crate::leanh::LeanObject,
    mut v_depth_5010_: *mut crate::leanh::LeanObject,
    mut v_keys_5011_: *mut crate::leanh::LeanObject,
    mut v_vals_5012_: *mut crate::leanh::LeanObject,
    mut v_heq_5013_: *mut crate::leanh::LeanObject,
    mut v_i_5014_: *mut crate::leanh::LeanObject,
    mut v_entries_5015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5016_: usize = 0;
    let mut v_res_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5016_ = crate::leanh::lean_unbox_usize(v_depth_5010_);
    crate::leanh::lean_dec(v_depth_5010_);
    v_res_5017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__5(v_00_u03b2_5009_, v_depth_boxed_5016_, v_keys_5011_, v_vals_5012_, v_heq_5013_, v_i_5014_, v_entries_5015_);
    crate::leanh::lean_dec_ref(v_vals_5012_);
    crate::leanh::lean_dec_ref(v_keys_5011_);
    return v_res_5017_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_5018_: *mut crate::leanh::LeanObject,
    mut v_x_5019_: *mut crate::leanh::LeanObject,
    mut v_x_5020_: *mut crate::leanh::LeanObject,
    mut v_x_5021_: *mut crate::leanh::LeanObject,
    mut v_x_5022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5023_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_isDefEqI_spec__1_spec__2_spec__4_spec__5___redArg(v_x_5019_, v_x_5020_, v_x_5021_, v_x_5022_);
    return v___x_5023_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5024_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5024_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__0_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__0,
    );
    v___x_5026_ = l_StateRefT_x27_instMonad___redArg(v___x_5025_);
    return v___x_5026_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5031_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_5032_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5032_, 0, v___x_5031_);
    return v___f_5032_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lean_instMonadExceptOfExceptionCoreM;
    v___f_5034_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5034_, 0, v___x_5033_);
    return v___f_5034_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5035_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__7_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__7,
    );
    v___f_5036_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__6_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__6,
    );
    v___x_5037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5037_, 0, v___f_5036_);
    crate::leanh::lean_ctor_set(v___x_5037_, 1, v___f_5035_);
    return v___x_5037_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8,
    );
    v___f_5039_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5039_, 0, v___x_5038_);
    return v___f_5039_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__8_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__8,
    );
    v___f_5041_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5041_, 0, v___x_5040_);
    return v___f_5041_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__10_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__10,
    );
    v___f_5043_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__9_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__9,
    );
    v___x_5044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5044_, 0, v___f_5043_);
    crate::leanh::lean_ctor_set(v___x_5044_, 1, v___f_5042_);
    return v___x_5044_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11,
    );
    v___f_5046_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5046_, 0, v___x_5045_);
    return v___f_5046_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__11_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__11,
    );
    v___f_5048_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5048_, 0, v___x_5047_);
    return v___f_5048_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__13_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__13,
    );
    v___f_5050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__12_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__12,
    );
    v___x_5051_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5051_, 0, v___f_5050_);
    crate::leanh::lean_ctor_set(v___x_5051_, 1, v___f_5049_);
    return v___x_5051_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14,
    );
    v___f_5053_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5053_, 0, v___x_5052_);
    return v___f_5053_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__14_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__14,
    );
    v___f_5055_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5055_, 0, v___x_5054_);
    return v___f_5055_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__16_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__16,
    );
    v___f_5057_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__15_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__15,
    );
    v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5058_, 0, v___f_5057_);
    crate::leanh::lean_ctor_set(v___x_5058_, 1, v___f_5056_);
    return v___x_5058_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__22() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__23() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5067_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__24() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5071_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5075_ = crate::leanh::lean_obj_once(
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
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5079_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__21;
    v___x_5080_ = l_Lean_Meta_instAddMessageContextMetaM;
    v___f_5081_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5081_, 0, v___x_5080_);
    crate::leanh::lean_closure_set(v___f_5081_, 1, v___x_5079_);
    return v___f_5081_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27() -> *mut crate::leanh::LeanObject
{
    let mut v___f_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5082_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__19;
    v___f_5083_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__26_once),
        _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__26,
    );
    v___f_5084_ = crate::leanh::lean_alloc_closure(
        l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5084_, 0, v___f_5083_);
    crate::leanh::lean_closure_set(v___f_5084_, 1, v___f_5082_);
    return v___f_5084_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__29() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__28;
    v___x_5087_ = l_Lean_stringToMessageData(v___x_5086_);
    return v___x_5087_;
}
pub unsafe fn l_Lean_Meta_Sym_instInhabitedSymM(
    mut v_00_u03b1_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v_toFunctor_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v___f_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMonadRef_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5141_: u8 = 0;
    let mut v_unused_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_unused_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5089_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__1_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__1,
                );
                v_toApplicative_5090_ = crate::leanh::lean_ctor_get(v___x_5089_, 0);
                v_toFunctor_5091_ = crate::leanh::lean_ctor_get(v_toApplicative_5090_, 0);
                v_toSeq_5092_ = crate::leanh::lean_ctor_get(v_toApplicative_5090_, 2);
                v_toSeqLeft_5093_ = crate::leanh::lean_ctor_get(v_toApplicative_5090_, 3);
                v_toSeqRight_5094_ = crate::leanh::lean_ctor_get(v_toApplicative_5090_, 4);
                v___f_5095_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__2;
                v___f_5096_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5091_, 2);
                v___f_5097_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5097_, 0, v_toFunctor_5091_);
                v___f_5098_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5098_, 0, v_toFunctor_5091_);
                v___x_5099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5099_, 0, v___f_5097_);
                crate::leanh::lean_ctor_set(v___x_5099_, 1, v___f_5098_);
                crate::leanh::lean_inc(v_toSeqRight_5094_);
                v___f_5100_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5100_, 0, v_toSeqRight_5094_);
                crate::leanh::lean_inc(v_toSeqLeft_5093_);
                v___f_5101_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5101_, 0, v_toSeqLeft_5093_);
                crate::leanh::lean_inc(v_toSeq_5092_);
                v___f_5102_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5102_, 0, v_toSeq_5092_);
                v___x_5103_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5103_, 0, v___x_5099_);
                crate::leanh::lean_ctor_set(v___x_5103_, 1, v___f_5095_);
                crate::leanh::lean_ctor_set(v___x_5103_, 2, v___f_5102_);
                crate::leanh::lean_ctor_set(v___x_5103_, 3, v___f_5101_);
                crate::leanh::lean_ctor_set(v___x_5103_, 4, v___f_5100_);
                v___x_5104_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5104_, 0, v___x_5103_);
                crate::leanh::lean_ctor_set(v___x_5104_, 1, v___f_5096_);
                v___x_5105_ = l_StateRefT_x27_instMonad___redArg(v___x_5104_);
                v_toApplicative_5106_ = crate::leanh::lean_ctor_get(v___x_5105_, 0);
                v_isSharedCheck_5143_ = (!crate::leanh::lean_is_exclusive(v___x_5105_)) as u8;
                if v_isSharedCheck_5143_ == 0 {
                    v_unused_5144_ = crate::leanh::lean_ctor_get(v___x_5105_, 1);
                    crate::leanh::lean_dec(v_unused_5144_);
                    v___x_5108_ = v___x_5105_;
                    v_isShared_5109_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5106_);
                    crate::leanh::lean_dec(v___x_5105_);
                    v___x_5108_ = crate::leanh::lean_box(0);
                    v_isShared_5109_ = v_isSharedCheck_5143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5110_ = crate::leanh::lean_ctor_get(v_toApplicative_5106_, 0);
                v_toSeq_5111_ = crate::leanh::lean_ctor_get(v_toApplicative_5106_, 2);
                v_toSeqLeft_5112_ = crate::leanh::lean_ctor_get(v_toApplicative_5106_, 3);
                v_toSeqRight_5113_ = crate::leanh::lean_ctor_get(v_toApplicative_5106_, 4);
                v_isSharedCheck_5141_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5106_)) as u8;
                if v_isSharedCheck_5141_ == 0 {
                    v_unused_5142_ = crate::leanh::lean_ctor_get(v_toApplicative_5106_, 1);
                    crate::leanh::lean_dec(v_unused_5142_);
                    v___x_5115_ = v_toApplicative_5106_;
                    v_isShared_5116_ = v_isSharedCheck_5141_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5113_);
                    crate::leanh::lean_inc(v_toSeqLeft_5112_);
                    crate::leanh::lean_inc(v_toSeq_5111_);
                    crate::leanh::lean_inc(v_toFunctor_5110_);
                    crate::leanh::lean_dec(v_toApplicative_5106_);
                    v___x_5115_ = crate::leanh::lean_box(0);
                    v_isShared_5116_ = v_isSharedCheck_5141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5117_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__4;
                v___f_5118_ = l_Lean_Meta_Sym_instInhabitedSymM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_5110_);
                v___f_5119_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5119_, 0, v_toFunctor_5110_);
                v___f_5120_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5120_, 0, v_toFunctor_5110_);
                v___x_5121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5121_, 0, v___f_5119_);
                crate::leanh::lean_ctor_set(v___x_5121_, 1, v___f_5120_);
                v___f_5122_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5122_, 0, v_toSeqRight_5113_);
                v___f_5123_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5123_, 0, v_toSeqLeft_5112_);
                v___f_5124_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5124_, 0, v_toSeq_5111_);
                if v_isShared_5116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5115_, 4, v___f_5122_);
                    crate::leanh::lean_ctor_set(v___x_5115_, 3, v___f_5123_);
                    crate::leanh::lean_ctor_set(v___x_5115_, 2, v___f_5124_);
                    crate::leanh::lean_ctor_set(v___x_5115_, 1, v___f_5117_);
                    crate::leanh::lean_ctor_set(v___x_5115_, 0, v___x_5121_);
                    v___x_5126_ = v___x_5115_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5140_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 1, v___f_5117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 2, v___f_5124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 3, v___f_5123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5140_, 4, v___f_5122_);
                    v___x_5126_ = v_reuseFailAlloc_5140_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5108_, 1, v___f_5118_);
                    crate::leanh::lean_ctor_set(v___x_5108_, 0, v___x_5126_);
                    v___x_5128_ = v___x_5108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v___x_5126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 1, v___f_5118_);
                    v___x_5128_ = v_reuseFailAlloc_5139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5129_ = l_StateRefT_x27_instMonad___redArg(v___x_5128_);
                v___x_5130_ = l_ReaderT_instMonad___redArg(v___x_5129_);
                v___x_5131_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__17_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__17,
                );
                v___x_5132_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__25),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__25_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__25,
                );
                v_toMonadRef_5133_ = crate::leanh::lean_ctor_get(v___x_5132_, 0);
                v___f_5134_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__27),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instInhabitedSymM___closed__27_once),
                    _init_l_Lean_Meta_Sym_instInhabitedSymM___closed__27,
                );
                crate::leanh::lean_inc_ref(v___x_5130_);
                v___x_5135_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(
                    v___f_5134_,
                    v___x_5130_,
                );
                crate::leanh::lean_inc_ref(v_toMonadRef_5133_);
                v___x_5136_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5136_, 0, v___x_5131_);
                crate::leanh::lean_ctor_set(v___x_5136_, 1, v_toMonadRef_5133_);
                crate::leanh::lean_ctor_set(v___x_5136_, 2, v___x_5135_);
                v___x_5137_ = crate::leanh::lean_obj_once(
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
    mut v_ext_5145_: *mut crate::leanh::LeanObject,
    mut v_extensions_5146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_id_5148_ = crate::leanh::lean_ctor_get(v_ext_5145_, 0);
    v___x_5149_ = l_Lean_Meta_Sym_instInhabitedSymExtensionState;
    v___x_5150_ = lean_array_get_borrowed(v___x_5149_, v_extensions_5146_, v_id_5148_);
    crate::leanh::lean_inc(v___x_5150_);
    v___x_5151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5151_, 0, v___x_5150_);
    return v___x_5151_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg___boxed(
    mut v_ext_5152_: *mut crate::leanh::LeanObject,
    mut v_extensions_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5155_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(
            v_ext_5152_,
            v_extensions_5153_,
        );
    crate::leanh::lean_dec_ref(v_extensions_5153_);
    crate::leanh::lean_dec_ref(v_ext_5152_);
    return v_res_5155_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(
    mut v_00_u03c3_5156_: *mut crate::leanh::LeanObject,
    mut v_ext_5157_: *mut crate::leanh::LeanObject,
    mut v_extensions_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5160_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(
            v_ext_5157_,
            v_extensions_5158_,
        );
    return v___x_5160_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___boxed(
    mut v_00_u03c3_5161_: *mut crate::leanh::LeanObject,
    mut v_ext_5162_: *mut crate::leanh::LeanObject,
    mut v_extensions_5163_: *mut crate::leanh::LeanObject,
    mut v_a_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5165_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl(
        v_00_u03c3_5161_,
        v_ext_5162_,
        v_extensions_5163_,
    );
    crate::leanh::lean_dec_ref(v_extensions_5163_);
    crate::leanh::lean_dec_ref(v_ext_5162_);
    return v_res_5165_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState___redArg(
    mut v_ext_5166_: *mut crate::leanh::LeanObject,
    mut v_a_5167_: *mut crate::leanh::LeanObject,
    mut v_a_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v_ref_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = lean_st_ref_get(v_a_5167_);
                v_extensions_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 7);
                crate::leanh::lean_inc_ref(v_extensions_5171_);
                crate::leanh::lean_dec(v___x_5170_);
                v___x_5172_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_getStateCoreImpl___redArg(v_ext_5166_, v_extensions_5171_);
                crate::leanh::lean_dec_ref(v_extensions_5171_);
                if crate::leanh::lean_obj_tag(v___x_5172_) == 0 {
                    v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                    v_isSharedCheck_5180_ = (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                    if v_isSharedCheck_5180_ == 0 {
                        v___x_5175_ = v___x_5172_;
                        v_isShared_5176_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5173_);
                        crate::leanh::lean_dec(v___x_5172_);
                        v___x_5175_ = crate::leanh::lean_box(0);
                        v_isShared_5176_ = v_isSharedCheck_5180_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5181_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                    v_isSharedCheck_5193_ = (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                    if v_isSharedCheck_5193_ == 0 {
                        v___x_5183_ = v___x_5172_;
                        v_isShared_5184_ = v_isSharedCheck_5193_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5181_);
                        crate::leanh::lean_dec(v___x_5172_);
                        v___x_5183_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5178_;
            }
            3 => {
                v_ref_5185_ = crate::leanh::lean_ctor_get(v_a_5168_, 5);
                v___x_5186_ = lean_io_error_to_string(v_a_5181_);
                v___x_5187_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5187_, 0, v___x_5186_);
                v___x_5188_ = l_Lean_MessageData_ofFormat(v___x_5187_);
                crate::leanh::lean_inc(v_ref_5185_);
                v___x_5189_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5189_, 0, v_ref_5185_);
                crate::leanh::lean_ctor_set(v___x_5189_, 1, v___x_5188_);
                if v_isShared_5184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5183_, 0, v___x_5189_);
                    v___x_5191_ = v___x_5183_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___x_5189_);
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
    mut v_ext_5194_: *mut crate::leanh::LeanObject,
    mut v_a_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5198_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5194_, v_a_5195_, v_a_5196_);
    crate::leanh::lean_dec_ref(v_a_5196_);
    crate::leanh::lean_dec(v_a_5195_);
    crate::leanh::lean_dec_ref(v_ext_5194_);
    return v_res_5198_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState(
    mut v_00_u03c3_5199_: *mut crate::leanh::LeanObject,
    mut v_ext_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
    mut v_a_5202_: *mut crate::leanh::LeanObject,
    mut v_a_5203_: *mut crate::leanh::LeanObject,
    mut v_a_5204_: *mut crate::leanh::LeanObject,
    mut v_a_5205_: *mut crate::leanh::LeanObject,
    mut v_a_5206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5208_ = l_Lean_Meta_Sym_SymExtension_getState___redArg(v_ext_5200_, v_a_5202_, v_a_5205_);
    return v___x_5208_;
}
pub unsafe fn l_Lean_Meta_Sym_SymExtension_getState___boxed(
    mut v_00_u03c3_5209_: *mut crate::leanh::LeanObject,
    mut v_ext_5210_: *mut crate::leanh::LeanObject,
    mut v_a_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
    mut v_a_5213_: *mut crate::leanh::LeanObject,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_5216_);
    crate::leanh::lean_dec_ref(v_a_5215_);
    crate::leanh::lean_dec(v_a_5214_);
    crate::leanh::lean_dec_ref(v_a_5213_);
    crate::leanh::lean_dec(v_a_5212_);
    crate::leanh::lean_dec_ref(v_a_5211_);
    crate::leanh::lean_dec_ref(v_ext_5210_);
    return v_res_5218_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
    mut v_ext_5219_: *mut crate::leanh::LeanObject,
    mut v_f_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_5234_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5237_: u8 = 0;
    let mut v_id_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v_v_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5223_ = lean_st_ref_take(v_a_5221_);
                v_share_5224_ = crate::leanh::lean_ctor_get(v___x_5223_, 0);
                v_maxFVar_5225_ = crate::leanh::lean_ctor_get(v___x_5223_, 1);
                v_proofInstInfo_5226_ = crate::leanh::lean_ctor_get(v___x_5223_, 2);
                v_inferType_5227_ = crate::leanh::lean_ctor_get(v___x_5223_, 3);
                v_getLevel_5228_ = crate::leanh::lean_ctor_get(v___x_5223_, 4);
                v_congrInfo_5229_ = crate::leanh::lean_ctor_get(v___x_5223_, 5);
                v_defEqI_5230_ = crate::leanh::lean_ctor_get(v___x_5223_, 6);
                v_extensions_5231_ = crate::leanh::lean_ctor_get(v___x_5223_, 7);
                v_issues_5232_ = crate::leanh::lean_ctor_get(v___x_5223_, 8);
                v_canon_5233_ = crate::leanh::lean_ctor_get(v___x_5223_, 9);
                v_debug_5234_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5223_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_5253_ = (!crate::leanh::lean_is_exclusive(v___x_5223_)) as u8;
                if v_isSharedCheck_5253_ == 0 {
                    v___x_5236_ = v___x_5223_;
                    v_isShared_5237_ = v_isSharedCheck_5253_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_5233_);
                    crate::leanh::lean_inc(v_issues_5232_);
                    crate::leanh::lean_inc(v_extensions_5231_);
                    crate::leanh::lean_inc(v_defEqI_5230_);
                    crate::leanh::lean_inc(v_congrInfo_5229_);
                    crate::leanh::lean_inc(v_getLevel_5228_);
                    crate::leanh::lean_inc(v_inferType_5227_);
                    crate::leanh::lean_inc(v_proofInstInfo_5226_);
                    crate::leanh::lean_inc(v_maxFVar_5225_);
                    crate::leanh::lean_inc(v_share_5224_);
                    crate::leanh::lean_dec(v___x_5223_);
                    v___x_5236_ = crate::leanh::lean_box(0);
                    v_isShared_5237_ = v_isSharedCheck_5253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_5238_ = crate::leanh::lean_ctor_get(v_ext_5219_, 0);
                v___x_5239_ = crate::leanh::lean_box(0);
                v___x_5247_ = lean_array_get_size(v_extensions_5231_);
                v___x_5248_ = lean_nat_dec_lt(v_id_5238_, v___x_5247_);
                if v___x_5248_ == 0 {
                    crate::leanh::lean_dec(v_f_5220_);
                    v___y_5241_ = v_extensions_5231_;
                    state = 2;
                    continue;
                } else {
                    v_v_5249_ = lean_array_fget(v_extensions_5231_, v_id_5238_);
                    v_xs_x27_5250_ = lean_array_fset(v_extensions_5231_, v_id_5238_, v___x_5239_);
                    v___x_5251_ = crate::leanh::lean_apply_1(v_f_5220_, v_v_5249_);
                    v___x_5252_ = lean_array_fset(v_xs_x27_5250_, v_id_5238_, v___x_5251_);
                    v___y_5241_ = v___x_5252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5236_, 7, v___y_5241_);
                    v___x_5243_ = v___x_5236_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_share_5224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_maxFVar_5225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_proofInstInfo_5226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_inferType_5227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 4, v_getLevel_5228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 5, v_congrInfo_5229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 6, v_defEqI_5230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 7, v___y_5241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 8, v_issues_5232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 9, v_canon_5233_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5246_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_5234_,
                    );
                    v___x_5243_ = v_reuseFailAlloc_5246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5244_ = lean_st_ref_set(v_a_5221_, v___x_5243_);
                v___x_5245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5245_, 0, v___x_5239_);
                return v___x_5245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg___boxed(
    mut v_ext_5254_: *mut crate::leanh::LeanObject,
    mut v_f_5255_: *mut crate::leanh::LeanObject,
    mut v_a_5256_: *mut crate::leanh::LeanObject,
    mut v_a_5257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5258_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v_ext_5254_,
            v_f_5255_,
            v_a_5256_,
        );
    crate::leanh::lean_dec(v_a_5256_);
    crate::leanh::lean_dec_ref(v_ext_5254_);
    return v_res_5258_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl(
    mut v_00_u03c3_5259_: *mut crate::leanh::LeanObject,
    mut v_ext_5260_: *mut crate::leanh::LeanObject,
    mut v_f_5261_: *mut crate::leanh::LeanObject,
    mut v_a_5262_: *mut crate::leanh::LeanObject,
    mut v_a_5263_: *mut crate::leanh::LeanObject,
    mut v_a_5264_: *mut crate::leanh::LeanObject,
    mut v_a_5265_: *mut crate::leanh::LeanObject,
    mut v_a_5266_: *mut crate::leanh::LeanObject,
    mut v_a_5267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5269_ =
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(
            v_ext_5260_,
            v_f_5261_,
            v_a_5263_,
        );
    return v___x_5269_;
}
pub unsafe fn l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___boxed(
    mut v_00_u03c3_5270_: *mut crate::leanh::LeanObject,
    mut v_ext_5271_: *mut crate::leanh::LeanObject,
    mut v_f_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
    mut v_a_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_a_5278_);
    crate::leanh::lean_dec_ref(v_a_5277_);
    crate::leanh::lean_dec(v_a_5276_);
    crate::leanh::lean_dec_ref(v_a_5275_);
    crate::leanh::lean_dec(v_a_5274_);
    crate::leanh::lean_dec_ref(v_a_5273_);
    crate::leanh::lean_dec_ref(v_ext_5271_);
    return v_res_5280_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_3481378630____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Sym_sym_debug = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Sym_sym_debug);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_2410647589____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_instInhabitedSymExtensionState =
        _init_l_Lean_Meta_Sym_instInhabitedSymExtensionState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedSymExtensionState);
    res = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_initFn_00___x40_Lean_Meta_Sym_SymM_1317853661____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_symExtensionsRef,
    );
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Sym_instInhabitedConfig_default =
        _init_l_Lean_Meta_Sym_instInhabitedConfig_default();
    l_Lean_Meta_Sym_instInhabitedConfig = _init_l_Lean_Meta_Sym_instInhabitedConfig();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_SymM(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CongrTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_SymM(builtin);
}
