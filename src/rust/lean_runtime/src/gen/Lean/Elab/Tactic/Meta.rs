// Lean compiler output
// Module: Lean.Elab.Tactic.Meta
// Imports: Lean.Elab.SyntheticMVars
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_instInhabitedPersistentArrayNode_default;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::{
    initialize_Lean_Elab_SyntheticMVars,
    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp,
    runtime_initialize_Lean_Elab_SyntheticMVars,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_pruneSolvedGoals,
    l_Lean_Elab_Tactic_run___boxed,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_TermElabM_run___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_mkAuxDecl, l_Lean_LocalContext_mkLetDecl, l_Lean_LocalContext_mkLocalDecl,
    l_Lean_instInhabitedLocalContext_default,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_instantiateMVarsCore,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::ShareCommon::lean_sharecommon_quick;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_usize, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 118, 97, 114, 67, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 76, 67, 116, 120, 77, 86, 97, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2_value: LeanStringObject<55> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 97, 115, 115, 111, 99, 105, 97, 116, 101, 100, 32, 102, 117, 108, 108, 32, 110, 97, 109, 101, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_runTactic___lam__0(
    mut v_tacticCode_904_: *mut LeanObject,
    mut v___y_905_: *mut LeanObject,
    mut v___y_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
    mut v___y_912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = l_Lean_Elab_Tactic_evalTactic(
        v_tacticCode_904_,
        v___y_905_,
        v___y_906_,
        v___y_907_,
        v___y_908_,
        v___y_909_,
        v___y_910_,
        v___y_911_,
        v___y_912_,
    );
    if lean_obj_tag(v___x_914_) == 0 {
        let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_914_, 1);
        v___x_915_ = l_Lean_Elab_Tactic_pruneSolvedGoals(
            v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_,
            v___y_912_,
        );
        return v___x_915_;
    } else {
        return v___x_914_;
    }
}
pub unsafe fn l_Lean_Elab_runTactic___lam__0___boxed(
    mut v_tacticCode_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
    mut v___y_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
    mut v___y_921_: *mut LeanObject,
    mut v___y_922_: *mut LeanObject,
    mut v___y_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_926_: *mut LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_Elab_runTactic___lam__0(
        v_tacticCode_916_,
        v___y_917_,
        v___y_918_,
        v___y_919_,
        v___y_920_,
        v___y_921_,
        v___y_922_,
        v___y_923_,
        v___y_924_,
    );
    lean_dec(v___y_924_);
    lean_dec_ref(v___y_923_);
    lean_dec(v___y_922_);
    lean_dec_ref(v___y_921_);
    lean_dec(v___y_920_);
    lean_dec_ref(v___y_919_);
    lean_dec(v___y_918_);
    lean_dec_ref(v___y_917_);
    return v_res_926_;
}
pub unsafe fn l_Lean_Elab_runTactic___lam__1(
    mut v___x_927_: *mut LeanObject,
    mut v___x_928_: u8,
    mut v___y_929_: *mut LeanObject,
    mut v___y_930_: *mut LeanObject,
    mut v___y_931_: *mut LeanObject,
    mut v___y_932_: *mut LeanObject,
    mut v___y_933_: *mut LeanObject,
    mut v___y_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    v___x_936_ = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
        lean_box(0),
        v___x_927_,
        v___x_928_,
        v___y_929_,
        v___y_930_,
        v___y_931_,
        v___y_932_,
        v___y_933_,
        v___y_934_,
    );
    return v___x_936_;
}
pub unsafe fn l_Lean_Elab_runTactic___lam__1___boxed(
    mut v___x_937_: *mut LeanObject,
    mut v___x_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
    mut v___y_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
    mut v___y_942_: *mut LeanObject,
    mut v___y_943_: *mut LeanObject,
    mut v___y_944_: *mut LeanObject,
    mut v___y_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5196__boxed_946_: u8 = 0;
    let mut v_res_947_: *mut LeanObject = core::ptr::null_mut();
    v___x_5196__boxed_946_ = (lean_unbox(v___x_938_) as u8);
    v_res_947_ = l_Lean_Elab_runTactic___lam__1(
        v___x_937_,
        v___x_5196__boxed_946_,
        v___y_939_,
        v___y_940_,
        v___y_941_,
        v___y_942_,
        v___y_943_,
        v___y_944_,
    );
    lean_dec(v___y_944_);
    lean_dec_ref(v___y_943_);
    lean_dec(v___y_942_);
    lean_dec_ref(v___y_941_);
    lean_dec(v___y_940_);
    lean_dec_ref(v___y_939_);
    return v_res_947_;
}
pub unsafe fn _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v___x_948_ = l_instMonadEIO(lean_box(0));
    return v___x_948_;
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(
    mut v_msg_953_: *mut LeanObject,
    mut v___y_954_: *mut LeanObject,
    mut v___y_955_: *mut LeanObject,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_toFunctor_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_971_: u8 = 0;
    let mut v___f_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v_toFunctor_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___f_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498__overap_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1014_: u8 = 0;
    let mut v_unused_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1016_: u8 = 0;
    let mut v_unused_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut v_unused_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1022_: u8 = 0;
    let mut v_unused_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_959_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0_once), _init_l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__0);
                v___x_960_ = l_StateRefT_x27_instMonad___redArg(v___x_959_);
                v_toApplicative_961_ = lean_ctor_get(v___x_960_, 0);
                v_isSharedCheck_1022_ = (!lean_is_exclusive(v___x_960_)) as u8;
                if v_isSharedCheck_1022_ == 0 {
                    v_unused_1023_ = lean_ctor_get(v___x_960_, 1);
                    lean_dec(v_unused_1023_);
                    v___x_963_ = v___x_960_;
                    v_isShared_964_ = v_isSharedCheck_1022_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_961_);
                    lean_dec(v___x_960_);
                    v___x_963_ = lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_1022_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_965_ = lean_ctor_get(v_toApplicative_961_, 0);
                v_toSeq_966_ = lean_ctor_get(v_toApplicative_961_, 2);
                v_toSeqLeft_967_ = lean_ctor_get(v_toApplicative_961_, 3);
                v_toSeqRight_968_ = lean_ctor_get(v_toApplicative_961_, 4);
                v_isSharedCheck_1020_ = (!lean_is_exclusive(v_toApplicative_961_)) as u8;
                if v_isSharedCheck_1020_ == 0 {
                    v_unused_1021_ = lean_ctor_get(v_toApplicative_961_, 1);
                    lean_dec(v_unused_1021_);
                    v___x_970_ = v_toApplicative_961_;
                    v_isShared_971_ = v_isSharedCheck_1020_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_968_);
                    lean_inc(v_toSeqLeft_967_);
                    lean_inc(v_toSeq_966_);
                    lean_inc(v_toFunctor_965_);
                    lean_dec(v_toApplicative_961_);
                    v___x_970_ = lean_box(0);
                    v_isShared_971_ = v_isSharedCheck_1020_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_972_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__1;
                v___f_973_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__2;
                lean_inc_ref(v_toFunctor_965_);
                v___f_974_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_974_, 0, v_toFunctor_965_);
                v___f_975_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_975_, 0, v_toFunctor_965_);
                v___x_976_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_976_, 0, v___f_974_);
                lean_ctor_set(v___x_976_, 1, v___f_975_);
                v___f_977_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_977_, 0, v_toSeqRight_968_);
                v___f_978_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_978_, 0, v_toSeqLeft_967_);
                v___f_979_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_979_, 0, v_toSeq_966_);
                if v_isShared_971_ == 0 {
                    lean_ctor_set(v___x_970_, 4, v___f_977_);
                    lean_ctor_set(v___x_970_, 3, v___f_978_);
                    lean_ctor_set(v___x_970_, 2, v___f_979_);
                    lean_ctor_set(v___x_970_, 1, v___f_972_);
                    lean_ctor_set(v___x_970_, 0, v___x_976_);
                    v___x_981_ = v___x_970_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_976_);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___f_972_);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 2, v___f_979_);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 3, v___f_978_);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 4, v___f_977_);
                    v___x_981_ = v_reuseFailAlloc_1019_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_964_ == 0 {
                    lean_ctor_set(v___x_963_, 1, v___f_973_);
                    lean_ctor_set(v___x_963_, 0, v___x_981_);
                    v___x_983_ = v___x_963_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_981_);
                    lean_ctor_set(v_reuseFailAlloc_1018_, 1, v___f_973_);
                    v___x_983_ = v_reuseFailAlloc_1018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_984_ = l_StateRefT_x27_instMonad___redArg(v___x_983_);
                v_toApplicative_985_ = lean_ctor_get(v___x_984_, 0);
                v_isSharedCheck_1016_ = (!lean_is_exclusive(v___x_984_)) as u8;
                if v_isSharedCheck_1016_ == 0 {
                    v_unused_1017_ = lean_ctor_get(v___x_984_, 1);
                    lean_dec(v_unused_1017_);
                    v___x_987_ = v___x_984_;
                    v_isShared_988_ = v_isSharedCheck_1016_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_985_);
                    lean_dec(v___x_984_);
                    v___x_987_ = lean_box(0);
                    v_isShared_988_ = v_isSharedCheck_1016_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_989_ = lean_ctor_get(v_toApplicative_985_, 0);
                v_toSeq_990_ = lean_ctor_get(v_toApplicative_985_, 2);
                v_toSeqLeft_991_ = lean_ctor_get(v_toApplicative_985_, 3);
                v_toSeqRight_992_ = lean_ctor_get(v_toApplicative_985_, 4);
                v_isSharedCheck_1014_ = (!lean_is_exclusive(v_toApplicative_985_)) as u8;
                if v_isSharedCheck_1014_ == 0 {
                    v_unused_1015_ = lean_ctor_get(v_toApplicative_985_, 1);
                    lean_dec(v_unused_1015_);
                    v___x_994_ = v_toApplicative_985_;
                    v_isShared_995_ = v_isSharedCheck_1014_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_992_);
                    lean_inc(v_toSeqLeft_991_);
                    lean_inc(v_toSeq_990_);
                    lean_inc(v_toFunctor_989_);
                    lean_dec(v_toApplicative_985_);
                    v___x_994_ = lean_box(0);
                    v_isShared_995_ = v_isSharedCheck_1014_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_996_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__3;
                v___f_997_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___closed__4;
                lean_inc_ref(v_toFunctor_989_);
                v___f_998_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_998_, 0, v_toFunctor_989_);
                v___f_999_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_999_, 0, v_toFunctor_989_);
                v___x_1000_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1000_, 0, v___f_998_);
                lean_ctor_set(v___x_1000_, 1, v___f_999_);
                v___f_1001_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1001_, 0, v_toSeqRight_992_);
                v___f_1002_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1002_, 0, v_toSeqLeft_991_);
                v___f_1003_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1003_, 0, v_toSeq_990_);
                if v_isShared_995_ == 0 {
                    lean_ctor_set(v___x_994_, 4, v___f_1001_);
                    lean_ctor_set(v___x_994_, 3, v___f_1002_);
                    lean_ctor_set(v___x_994_, 2, v___f_1003_);
                    lean_ctor_set(v___x_994_, 1, v___f_996_);
                    lean_ctor_set(v___x_994_, 0, v___x_1000_);
                    v___x_1005_ = v___x_994_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1000_);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___f_996_);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___f_1003_);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 3, v___f_1002_);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 4, v___f_1001_);
                    v___x_1005_ = v_reuseFailAlloc_1013_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_988_ == 0 {
                    lean_ctor_set(v___x_987_, 1, v___f_997_);
                    lean_ctor_set(v___x_987_, 0, v___x_1005_);
                    v___x_1007_ = v___x_987_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1005_);
                    lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___f_997_);
                    v___x_1007_ = v_reuseFailAlloc_1012_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1008_ = l_Lean_instInhabitedLocalContext_default;
                v___x_1009_ = l_instInhabitedOfMonad___redArg(v___x_1007_, v___x_1008_);
                v___x_2498__overap_1010_ = lean_panic_fn_borrowed(v___x_1009_, v_msg_953_);
                lean_dec(v___x_1009_);
                lean_inc(v___y_957_);
                lean_inc_ref(v___y_956_);
                lean_inc(v___y_955_);
                lean_inc_ref(v___y_954_);
                v___x_1011_ = lean_apply_5(
                    v___x_2498__overap_1010_,
                    v___y_954_,
                    v___y_955_,
                    v___y_956_,
                    v___y_957_,
                    lean_box(0),
                );
                return v___x_1011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2___boxed(
    mut v_msg_1024_: *mut LeanObject,
    mut v___y_1025_: *mut LeanObject,
    mut v___y_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v_msg_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
    lean_dec(v___y_1028_);
    lean_dec_ref(v___y_1027_);
    lean_dec(v___y_1026_);
    lean_dec_ref(v___y_1025_);
    return v_res_1030_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(
    mut v_e_1031_: *mut LeanObject,
    mut v___y_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1054_: u8 = 0;
    let mut v_unused_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1034_ = l_Lean_Expr_hasMVar(v_e_1031_);
                if v___x_1034_ == 0 {
                    v___x_1035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1035_, 0, v_e_1031_);
                    return v___x_1035_;
                } else {
                    v___x_1036_ = lean_st_ref_get(v___y_1032_);
                    v_mctx_1037_ = lean_ctor_get(v___x_1036_, 0);
                    lean_inc_ref(v_mctx_1037_);
                    lean_dec(v___x_1036_);
                    v___x_1038_ = l_Lean_instantiateMVarsCore(v_mctx_1037_, v_e_1031_);
                    v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
                    lean_inc(v_fst_1039_);
                    v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
                    lean_inc(v_snd_1040_);
                    lean_dec_ref(v___x_1038_);
                    v___x_1041_ = lean_st_ref_take(v___y_1032_);
                    v_cache_1042_ = lean_ctor_get(v___x_1041_, 1);
                    v_zetaDeltaFVarIds_1043_ = lean_ctor_get(v___x_1041_, 2);
                    v_postponed_1044_ = lean_ctor_get(v___x_1041_, 3);
                    v_diag_1045_ = lean_ctor_get(v___x_1041_, 4);
                    v_isSharedCheck_1054_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1054_ == 0 {
                        v_unused_1055_ = lean_ctor_get(v___x_1041_, 0);
                        lean_dec(v_unused_1055_);
                        v___x_1047_ = v___x_1041_;
                        v_isShared_1048_ = v_isSharedCheck_1054_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1045_);
                        lean_inc(v_postponed_1044_);
                        lean_inc(v_zetaDeltaFVarIds_1043_);
                        lean_inc(v_cache_1042_);
                        lean_dec(v___x_1041_);
                        v___x_1047_ = lean_box(0);
                        v_isShared_1048_ = v_isSharedCheck_1054_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1048_ == 0 {
                    lean_ctor_set(v___x_1047_, 0, v_snd_1040_);
                    v___x_1050_ = v___x_1047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_snd_1040_);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_cache_1042_);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 2, v_zetaDeltaFVarIds_1043_);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 3, v_postponed_1044_);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 4, v_diag_1045_);
                    v___x_1050_ = v_reuseFailAlloc_1053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1051_ = lean_st_ref_set(v___y_1032_, v___x_1050_);
                v___x_1052_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1052_, 0, v_fst_1039_);
                return v___x_1052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg___boxed(
    mut v_e_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1059_: *mut LeanObject = core::ptr::null_mut();
    v_res_1059_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_1056_, v___y_1057_);
    lean_dec(v___y_1057_);
    return v_res_1059_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(
    mut v_t_1060_: *mut LeanObject,
    mut v_k_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1060_) == 0 {
                    v_k_1062_ = lean_ctor_get(v_t_1060_, 1);
                    v_v_1063_ = lean_ctor_get(v_t_1060_, 2);
                    v_l_1064_ = lean_ctor_get(v_t_1060_, 3);
                    v_r_1065_ = lean_ctor_get(v_t_1060_, 4);
                    v___x_1066_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1061_, v_k_1062_);
                    match v___x_1066_ {
                        0 => {
                            v_t_1060_ = v_l_1064_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1063_);
                            v___x_1068_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1068_, 0, v_v_1063_);
                            return v___x_1068_;
                        }
                        _ => {
                            v_t_1060_ = v_r_1065_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1070_ = lean_box(0);
                    return v___x_1070_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_t_1071_: *mut LeanObject,
    mut v_k_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1073_: *mut LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_1071_, v_k_1072_);
    lean_dec(v_k_1072_);
    lean_dec(v_t_1071_);
    return v_res_1073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(
    mut v_auxDeclToFullName_1078_: *mut LeanObject,
    mut v_as_1079_: *mut LeanObject,
    mut v_i_1080_: usize,
    mut v_stop_1081_: usize,
    mut v_b_1082_: *mut LeanObject,
    mut v___y_1083_: *mut LeanObject,
    mut v___y_1084_: *mut LeanObject,
    mut v___y_1085_: *mut LeanObject,
    mut v___y_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: usize = 0;
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1096_: u8 = 0;
    let mut v_fvarId_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: u8 = 0;
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1121_: u8 = 0;
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut v_fvarId_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bi_1129_: u8 = 0;
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1136_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_fvarId_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_1145_: u8 = 0;
    let mut v_kind_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_a_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_usize_dec_eq(v_i_1080_, v_stop_1081_);
                if v___x_1093_ == 0 {
                    v___x_1094_ = lean_array_uget_borrowed(v_as_1079_, v_i_1080_);
                    if lean_obj_tag(v___x_1094_) == 0 {
                        v_a_1089_ = v_b_1082_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1095_ = lean_ctor_get(v___x_1094_, 0);
                        if lean_obj_tag(v_val_1095_) == 0 {
                            v_kind_1096_ = lean_ctor_get_uint8(
                                v_val_1095_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                            );
                            if v_kind_1096_ == 2 {
                                v_fvarId_1097_ = lean_ctor_get(v_val_1095_, 1);
                                v_userName_1098_ = lean_ctor_get(v_val_1095_, 2);
                                v_type_1099_ = lean_ctor_get(v_val_1095_, 3);
                                lean_inc_ref(v_type_1099_);
                                v___x_1100_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_1099_, v___y_1084_);
                                if lean_obj_tag(v___x_1100_) == 0 {
                                    v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
                                    lean_inc(v_a_1101_);
                                    lean_dec_ref_known(v___x_1100_, 1);
                                    v___x_1102_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_auxDeclToFullName_1078_, v_fvarId_1097_);
                                    if lean_obj_tag(v___x_1102_) == 1 {
                                        v_val_1103_ = lean_ctor_get(v___x_1102_, 0);
                                        lean_inc(v_val_1103_);
                                        lean_dec_ref_known(v___x_1102_, 1);
                                        lean_inc(v_userName_1098_);
                                        lean_inc(v_fvarId_1097_);
                                        v___x_1104_ = l_Lean_LocalContext_mkAuxDecl(
                                            v_b_1082_,
                                            v_fvarId_1097_,
                                            v_userName_1098_,
                                            v_a_1101_,
                                            v_val_1103_,
                                        );
                                        v_a_1089_ = v___x_1104_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v___x_1102_);
                                        lean_dec(v_a_1101_);
                                        lean_dec_ref(v_b_1082_);
                                        v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__0;
                                        v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__1;
                                        v___x_1107_ = lean_unsigned_to_nat(635);
                                        v___x_1108_ = lean_unsigned_to_nat(12);
                                        v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__2;
                                        v___x_1110_ = 1;
                                        lean_inc(v_userName_1098_);
                                        v___x_1111_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_1098_, v___x_1110_);
                                        v___x_1112_ = lean_string_append(v___x_1109_, v___x_1111_);
                                        lean_dec_ref(v___x_1111_);
                                        v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___closed__3;
                                        v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
                                        v___x_1115_ = l_mkPanicMessageWithDecl(
                                            v___x_1105_,
                                            v___x_1106_,
                                            v___x_1107_,
                                            v___x_1108_,
                                            v___x_1114_,
                                        );
                                        lean_dec_ref(v___x_1114_);
                                        v___x_1116_ = l_panic___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__2(v___x_1115_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
                                        if lean_obj_tag(v___x_1116_) == 0 {
                                            v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
                                            lean_inc(v_a_1117_);
                                            lean_dec_ref_known(v___x_1116_, 1);
                                            v_a_1089_ = v_a_1117_;
                                            state = 1;
                                            continue;
                                        } else {
                                            return v___x_1116_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_b_1082_);
                                    v_a_1118_ = lean_ctor_get(v___x_1100_, 0);
                                    v_isSharedCheck_1125_ = (!lean_is_exclusive(v___x_1100_)) as u8;
                                    if v_isSharedCheck_1125_ == 0 {
                                        v___x_1120_ = v___x_1100_;
                                        v_isShared_1121_ = v_isSharedCheck_1125_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1118_);
                                        lean_dec(v___x_1100_);
                                        v___x_1120_ = lean_box(0);
                                        v_isShared_1121_ = v_isSharedCheck_1125_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                v_fvarId_1126_ = lean_ctor_get(v_val_1095_, 1);
                                v_userName_1127_ = lean_ctor_get(v_val_1095_, 2);
                                v_type_1128_ = lean_ctor_get(v_val_1095_, 3);
                                v_bi_1129_ = lean_ctor_get_uint8(
                                    v_val_1095_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                );
                                lean_inc_ref(v_type_1128_);
                                v___x_1130_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_1128_, v___y_1084_);
                                if lean_obj_tag(v___x_1130_) == 0 {
                                    v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
                                    lean_inc(v_a_1131_);
                                    lean_dec_ref_known(v___x_1130_, 1);
                                    lean_inc(v_userName_1127_);
                                    lean_inc(v_fvarId_1126_);
                                    v___x_1132_ = l_Lean_LocalContext_mkLocalDecl(
                                        v_b_1082_,
                                        v_fvarId_1126_,
                                        v_userName_1127_,
                                        v_a_1131_,
                                        v_bi_1129_,
                                        v_kind_1096_,
                                    );
                                    v_a_1089_ = v___x_1132_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec_ref(v_b_1082_);
                                    v_a_1133_ = lean_ctor_get(v___x_1130_, 0);
                                    v_isSharedCheck_1140_ = (!lean_is_exclusive(v___x_1130_)) as u8;
                                    if v_isSharedCheck_1140_ == 0 {
                                        v___x_1135_ = v___x_1130_;
                                        v_isShared_1136_ = v_isSharedCheck_1140_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1133_);
                                        lean_dec(v___x_1130_);
                                        v___x_1135_ = lean_box(0);
                                        v_isShared_1136_ = v_isSharedCheck_1140_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_fvarId_1141_ = lean_ctor_get(v_val_1095_, 1);
                            v_userName_1142_ = lean_ctor_get(v_val_1095_, 2);
                            v_type_1143_ = lean_ctor_get(v_val_1095_, 3);
                            v_value_1144_ = lean_ctor_get(v_val_1095_, 4);
                            v_nondep_1145_ = lean_ctor_get_uint8(
                                v_val_1095_,
                                (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                            );
                            v_kind_1146_ = lean_ctor_get_uint8(
                                v_val_1095_,
                                (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                            );
                            lean_inc_ref(v_type_1143_);
                            v___x_1147_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_1143_, v___y_1084_);
                            if lean_obj_tag(v___x_1147_) == 0 {
                                v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
                                lean_inc(v_a_1148_);
                                lean_dec_ref_known(v___x_1147_, 1);
                                lean_inc_ref(v_value_1144_);
                                v___x_1149_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_value_1144_, v___y_1084_);
                                if lean_obj_tag(v___x_1149_) == 0 {
                                    v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
                                    lean_inc(v_a_1150_);
                                    lean_dec_ref_known(v___x_1149_, 1);
                                    lean_inc(v_userName_1142_);
                                    lean_inc(v_fvarId_1141_);
                                    v___x_1151_ = l_Lean_LocalContext_mkLetDecl(
                                        v_b_1082_,
                                        v_fvarId_1141_,
                                        v_userName_1142_,
                                        v_a_1148_,
                                        v_a_1150_,
                                        v_nondep_1145_,
                                        v_kind_1146_,
                                    );
                                    v_a_1089_ = v___x_1151_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_1148_);
                                    lean_dec_ref(v_b_1082_);
                                    v_a_1152_ = lean_ctor_get(v___x_1149_, 0);
                                    v_isSharedCheck_1159_ = (!lean_is_exclusive(v___x_1149_)) as u8;
                                    if v_isSharedCheck_1159_ == 0 {
                                        v___x_1154_ = v___x_1149_;
                                        v_isShared_1155_ = v_isSharedCheck_1159_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1152_);
                                        lean_dec(v___x_1149_);
                                        v___x_1154_ = lean_box(0);
                                        v_isShared_1155_ = v_isSharedCheck_1159_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_b_1082_);
                                v_a_1160_ = lean_ctor_get(v___x_1147_, 0);
                                v_isSharedCheck_1167_ = (!lean_is_exclusive(v___x_1147_)) as u8;
                                if v_isSharedCheck_1167_ == 0 {
                                    v___x_1162_ = v___x_1147_;
                                    v_isShared_1163_ = v_isSharedCheck_1167_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_1160_);
                                    lean_dec(v___x_1147_);
                                    v___x_1162_ = lean_box(0);
                                    v_isShared_1163_ = v_isSharedCheck_1167_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_1168_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1168_, 0, v_b_1082_);
                    return v___x_1168_;
                }
            }
            1 => {
                v___x_1090_ = 1usize;
                v___x_1091_ = lean_usize_add(v_i_1080_, v___x_1090_);
                v_i_1080_ = v___x_1091_;
                v_b_1082_ = v_a_1089_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1121_ == 0 {
                    v___x_1123_ = v___x_1120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1123_;
            }
            4 => {
                if v_isShared_1136_ == 0 {
                    v___x_1138_ = v___x_1135_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
                    v___x_1138_ = v_reuseFailAlloc_1139_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1138_;
            }
            6 => {
                if v_isShared_1155_ == 0 {
                    v___x_1157_ = v___x_1154_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1157_;
            }
            8 => {
                if v_isShared_1163_ == 0 {
                    v___x_1165_ = v___x_1162_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8___boxed(
    mut v_auxDeclToFullName_1169_: *mut LeanObject,
    mut v_as_1170_: *mut LeanObject,
    mut v_i_1171_: *mut LeanObject,
    mut v_stop_1172_: *mut LeanObject,
    mut v_b_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1179_: usize = 0;
    let mut v_stop_boxed_1180_: usize = 0;
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1179_ = lean_unbox_usize(v_i_1171_);
    lean_dec(v_i_1171_);
    v_stop_boxed_1180_ = lean_unbox_usize(v_stop_1172_);
    lean_dec(v_stop_1172_);
    v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1169_, v_as_1170_, v_i_boxed_1179_, v_stop_boxed_1180_, v_b_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
    lean_dec(v___y_1177_);
    lean_dec_ref(v___y_1176_);
    lean_dec(v___y_1175_);
    lean_dec_ref(v___y_1174_);
    lean_dec_ref(v_as_1170_);
    lean_dec(v_auxDeclToFullName_1169_);
    return v_res_1181_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(
    mut v_auxDeclToFullName_1182_: *mut LeanObject,
    mut v_x_1183_: *mut LeanObject,
    mut v_x_1184_: *mut LeanObject,
    mut v___y_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: usize = 0;
    let mut v___x_1205_: usize = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: usize = 0;
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1210_: u8 = 0;
    let mut v_vs_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: usize = 0;
    let mut v___x_1226_: usize = 0;
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: usize = 0;
    let mut v___x_1229_: usize = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1183_) == 0 {
                    v_cs_1190_ = lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1210_ = (!lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1210_ == 0 {
                        v___x_1192_ = v_x_1183_;
                        v_isShared_1193_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cs_1190_);
                        lean_dec(v_x_1183_);
                        v___x_1192_ = lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1210_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_1211_ = lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1231_ = (!lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1231_ == 0 {
                        v___x_1213_ = v_x_1183_;
                        v_isShared_1214_ = v_isSharedCheck_1231_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_vs_1211_);
                        lean_dec(v_x_1183_);
                        v___x_1213_ = lean_box(0);
                        v_isShared_1214_ = v_isSharedCheck_1231_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1194_ = lean_unsigned_to_nat(0);
                v___x_1195_ = lean_array_get_size(v_cs_1190_);
                v___x_1196_ = lean_nat_dec_lt(v___x_1194_, v___x_1195_);
                if v___x_1196_ == 0 {
                    lean_dec_ref(v_cs_1190_);
                    if v_isShared_1193_ == 0 {
                        lean_ctor_set(v___x_1192_, 0, v_x_1184_);
                        v___x_1198_ = v___x_1192_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_x_1184_);
                        v___x_1198_ = v_reuseFailAlloc_1199_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1200_ = lean_nat_dec_le(v___x_1195_, v___x_1195_);
                    if v___x_1200_ == 0 {
                        if v___x_1196_ == 0 {
                            lean_dec_ref(v_cs_1190_);
                            if v_isShared_1193_ == 0 {
                                lean_ctor_set(v___x_1192_, 0, v_x_1184_);
                                v___x_1202_ = v___x_1192_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_x_1184_);
                                v___x_1202_ = v_reuseFailAlloc_1203_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1192_);
                            v___x_1204_ = 0usize;
                            v___x_1205_ = lean_usize_of_nat(v___x_1195_);
                            v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_1182_, v_cs_1190_, v___x_1204_, v___x_1205_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
                            lean_dec_ref(v_cs_1190_);
                            return v___x_1206_;
                        }
                    } else {
                        lean_del_object(v___x_1192_);
                        v___x_1207_ = 0usize;
                        v___x_1208_ = lean_usize_of_nat(v___x_1195_);
                        v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_1182_, v_cs_1190_, v___x_1207_, v___x_1208_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
                        lean_dec_ref(v_cs_1190_);
                        return v___x_1209_;
                    }
                }
            }
            2 => {
                return v___x_1198_;
            }
            3 => {
                return v___x_1202_;
            }
            4 => {
                v___x_1215_ = lean_unsigned_to_nat(0);
                v___x_1216_ = lean_array_get_size(v_vs_1211_);
                v___x_1217_ = lean_nat_dec_lt(v___x_1215_, v___x_1216_);
                if v___x_1217_ == 0 {
                    lean_dec_ref(v_vs_1211_);
                    if v_isShared_1214_ == 0 {
                        lean_ctor_set_tag(v___x_1213_, 0);
                        lean_ctor_set(v___x_1213_, 0, v_x_1184_);
                        v___x_1219_ = v___x_1213_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_x_1184_);
                        v___x_1219_ = v_reuseFailAlloc_1220_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_1221_ = lean_nat_dec_le(v___x_1216_, v___x_1216_);
                    if v___x_1221_ == 0 {
                        if v___x_1217_ == 0 {
                            lean_dec_ref(v_vs_1211_);
                            if v_isShared_1214_ == 0 {
                                lean_ctor_set_tag(v___x_1213_, 0);
                                lean_ctor_set(v___x_1213_, 0, v_x_1184_);
                                v___x_1223_ = v___x_1213_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_x_1184_);
                                v___x_1223_ = v_reuseFailAlloc_1224_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1213_);
                            v___x_1225_ = 0usize;
                            v___x_1226_ = lean_usize_of_nat(v___x_1216_);
                            v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1182_, v_vs_1211_, v___x_1225_, v___x_1226_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
                            lean_dec_ref(v_vs_1211_);
                            return v___x_1227_;
                        }
                    } else {
                        lean_del_object(v___x_1213_);
                        v___x_1228_ = 0usize;
                        v___x_1229_ = lean_usize_of_nat(v___x_1216_);
                        v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1182_, v_vs_1211_, v___x_1228_, v___x_1229_, v_x_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
                        lean_dec_ref(v_vs_1211_);
                        return v___x_1230_;
                    }
                }
            }
            5 => {
                return v___x_1219_;
            }
            6 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(
    mut v_auxDeclToFullName_1232_: *mut LeanObject,
    mut v_as_1233_: *mut LeanObject,
    mut v_i_1234_: usize,
    mut v_stop_1235_: usize,
    mut v_b_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1242_: u8 = 0;
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: usize = 0;
    let mut v___x_1247_: usize = 0;
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_usize_dec_eq(v_i_1234_, v_stop_1235_);
                if v___x_1242_ == 0 {
                    v___x_1243_ = lean_array_uget_borrowed(v_as_1233_, v_i_1234_);
                    lean_inc(v___x_1243_);
                    v___x_1244_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_1232_, v___x_1243_, v_b_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
                    if lean_obj_tag(v___x_1244_) == 0 {
                        v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
                        lean_inc(v_a_1245_);
                        lean_dec_ref_known(v___x_1244_, 1);
                        v___x_1246_ = 1usize;
                        v___x_1247_ = lean_usize_add(v_i_1234_, v___x_1246_);
                        v_i_1234_ = v___x_1247_;
                        v_b_1236_ = v_a_1245_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1244_;
                    }
                } else {
                    v___x_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1249_, 0, v_b_1236_);
                    return v___x_1249_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9___boxed(
    mut v_auxDeclToFullName_1250_: *mut LeanObject,
    mut v_as_1251_: *mut LeanObject,
    mut v_i_1252_: *mut LeanObject,
    mut v_stop_1253_: *mut LeanObject,
    mut v_b_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1260_: usize = 0;
    let mut v_stop_boxed_1261_: usize = 0;
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1260_ = lean_unbox_usize(v_i_1252_);
    lean_dec(v_i_1252_);
    v_stop_boxed_1261_ = lean_unbox_usize(v_stop_1253_);
    lean_dec(v_stop_1253_);
    v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_1250_, v_as_1251_, v_i_boxed_1260_, v_stop_boxed_1261_, v_b_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
    lean_dec(v___y_1258_);
    lean_dec_ref(v___y_1257_);
    lean_dec(v___y_1256_);
    lean_dec_ref(v___y_1255_);
    lean_dec_ref(v_as_1251_);
    lean_dec(v_auxDeclToFullName_1250_);
    return v_res_1262_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9___boxed(
    mut v_auxDeclToFullName_1263_: *mut LeanObject,
    mut v_x_1264_: *mut LeanObject,
    mut v_x_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_1263_, v_x_1264_, v_x_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
    lean_dec(v___y_1269_);
    lean_dec_ref(v___y_1268_);
    lean_dec(v___y_1267_);
    lean_dec_ref(v___y_1266_);
    lean_dec(v_auxDeclToFullName_1263_);
    return v_res_1271_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0()
-> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    v___x_1272_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
    return v___x_1272_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(
    mut v_auxDeclToFullName_1273_: *mut LeanObject,
    mut v_x_1274_: *mut LeanObject,
    mut v_x_1275_: usize,
    mut v_x_1276_: usize,
    mut v_x_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: usize = 0;
    let mut v_j_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: usize = 0;
    let mut v___x_1289_: usize = 0;
    let mut v___x_1290_: usize = 0;
    let mut v___x_1291_: usize = 0;
    let mut v___x_1292_: usize = 0;
    let mut v___x_1293_: usize = 0;
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: u8 = 0;
    let mut v___x_1301_: usize = 0;
    let mut v___x_1302_: usize = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: usize = 0;
    let mut v___x_1305_: usize = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: usize = 0;
    let mut v___x_1322_: usize = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: usize = 0;
    let mut v___x_1325_: usize = 0;
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1274_) == 0 {
                    v_cs_1283_ = lean_ctor_get(v_x_1274_, 0);
                    lean_inc_ref(v_cs_1283_);
                    lean_dec_ref_known(v_x_1274_, 1);
                    v___x_1284_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___closed__0);
                    v___x_1285_ = lean_usize_shift_right(v_x_1275_, v_x_1276_);
                    v_j_1286_ = lean_usize_to_nat(v___x_1285_);
                    v___x_1287_ = lean_array_get_borrowed(v___x_1284_, v_cs_1283_, v_j_1286_);
                    v___x_1288_ = 1usize;
                    v___x_1289_ = lean_usize_shift_left(v___x_1288_, v_x_1276_);
                    v___x_1290_ = lean_usize_sub(v___x_1289_, v___x_1288_);
                    v___x_1291_ = lean_usize_land(v_x_1275_, v___x_1290_);
                    v___x_1292_ = 5usize;
                    v___x_1293_ = lean_usize_sub(v_x_1276_, v___x_1292_);
                    lean_inc(v___x_1287_);
                    v___x_1294_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_1273_, v___x_1287_, v___x_1291_, v___x_1293_, v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                    if lean_obj_tag(v___x_1294_) == 0 {
                        v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
                        lean_inc(v_a_1295_);
                        v___x_1296_ = lean_unsigned_to_nat(1);
                        v___x_1297_ = lean_nat_add(v_j_1286_, v___x_1296_);
                        lean_dec(v_j_1286_);
                        v___x_1298_ = lean_array_get_size(v_cs_1283_);
                        v___x_1299_ = lean_nat_dec_lt(v___x_1297_, v___x_1298_);
                        if v___x_1299_ == 0 {
                            lean_dec(v___x_1297_);
                            lean_dec(v_a_1295_);
                            lean_dec_ref(v_cs_1283_);
                            return v___x_1294_;
                        } else {
                            v___x_1300_ = lean_nat_dec_le(v___x_1298_, v___x_1298_);
                            if v___x_1300_ == 0 {
                                if v___x_1299_ == 0 {
                                    lean_dec(v___x_1297_);
                                    lean_dec(v_a_1295_);
                                    lean_dec_ref(v_cs_1283_);
                                    return v___x_1294_;
                                } else {
                                    lean_dec_ref_known(v___x_1294_, 1);
                                    v___x_1301_ = lean_usize_of_nat(v___x_1297_);
                                    lean_dec(v___x_1297_);
                                    v___x_1302_ = lean_usize_of_nat(v___x_1298_);
                                    v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_1273_, v_cs_1283_, v___x_1301_, v___x_1302_, v_a_1295_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                                    lean_dec_ref(v_cs_1283_);
                                    return v___x_1303_;
                                }
                            } else {
                                lean_dec_ref_known(v___x_1294_, 1);
                                v___x_1304_ = lean_usize_of_nat(v___x_1297_);
                                lean_dec(v___x_1297_);
                                v___x_1305_ = lean_usize_of_nat(v___x_1298_);
                                v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7_spec__9(v_auxDeclToFullName_1273_, v_cs_1283_, v___x_1304_, v___x_1305_, v_a_1295_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                                lean_dec_ref(v_cs_1283_);
                                return v___x_1306_;
                            }
                        }
                    } else {
                        lean_dec(v_j_1286_);
                        lean_dec_ref(v_cs_1283_);
                        return v___x_1294_;
                    }
                } else {
                    v_vs_1307_ = lean_ctor_get(v_x_1274_, 0);
                    v_isSharedCheck_1327_ = (!lean_is_exclusive(v_x_1274_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v___x_1309_ = v_x_1274_;
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vs_1307_);
                        lean_dec(v_x_1274_);
                        v___x_1309_ = lean_box(0);
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1311_ = lean_usize_to_nat(v_x_1275_);
                v___x_1312_ = lean_array_get_size(v_vs_1307_);
                v___x_1313_ = lean_nat_dec_lt(v___x_1311_, v___x_1312_);
                if v___x_1313_ == 0 {
                    lean_dec(v___x_1311_);
                    lean_dec_ref(v_vs_1307_);
                    if v_isShared_1310_ == 0 {
                        lean_ctor_set_tag(v___x_1309_, 0);
                        lean_ctor_set(v___x_1309_, 0, v_x_1277_);
                        v___x_1315_ = v___x_1309_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_x_1277_);
                        v___x_1315_ = v_reuseFailAlloc_1316_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1317_ = lean_nat_dec_le(v___x_1312_, v___x_1312_);
                    if v___x_1317_ == 0 {
                        if v___x_1313_ == 0 {
                            lean_dec(v___x_1311_);
                            lean_dec_ref(v_vs_1307_);
                            if v_isShared_1310_ == 0 {
                                lean_ctor_set_tag(v___x_1309_, 0);
                                lean_ctor_set(v___x_1309_, 0, v_x_1277_);
                                v___x_1319_ = v___x_1309_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_x_1277_);
                                v___x_1319_ = v_reuseFailAlloc_1320_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1309_);
                            v___x_1321_ = lean_usize_of_nat(v___x_1311_);
                            lean_dec(v___x_1311_);
                            v___x_1322_ = lean_usize_of_nat(v___x_1312_);
                            v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1273_, v_vs_1307_, v___x_1321_, v___x_1322_, v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                            lean_dec_ref(v_vs_1307_);
                            return v___x_1323_;
                        }
                    } else {
                        lean_del_object(v___x_1309_);
                        v___x_1324_ = lean_usize_of_nat(v___x_1311_);
                        lean_dec(v___x_1311_);
                        v___x_1325_ = lean_usize_of_nat(v___x_1312_);
                        v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1273_, v_vs_1307_, v___x_1324_, v___x_1325_, v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
                        lean_dec_ref(v_vs_1307_);
                        return v___x_1326_;
                    }
                }
            }
            2 => {
                return v___x_1315_;
            }
            3 => {
                return v___x_1319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7___boxed(
    mut v_auxDeclToFullName_1328_: *mut LeanObject,
    mut v_x_1329_: *mut LeanObject,
    mut v_x_1330_: *mut LeanObject,
    mut v_x_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5752__boxed_1338_: usize = 0;
    let mut v_x_5753__boxed_1339_: usize = 0;
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_x_5752__boxed_1338_ = lean_unbox_usize(v_x_1330_);
    lean_dec(v_x_1330_);
    v_x_5753__boxed_1339_ = lean_unbox_usize(v_x_1331_);
    lean_dec(v_x_1331_);
    v_res_1340_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_1328_, v_x_1329_, v_x_5752__boxed_1338_, v_x_5753__boxed_1339_, v_x_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    lean_dec(v___y_1336_);
    lean_dec_ref(v___y_1335_);
    lean_dec(v___y_1334_);
    lean_dec_ref(v___y_1333_);
    lean_dec(v_auxDeclToFullName_1328_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(
    mut v_auxDeclToFullName_1341_: *mut LeanObject,
    mut v_t_1342_: *mut LeanObject,
    mut v_init_1343_: *mut LeanObject,
    mut v_start_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    v___x_1350_ = lean_unsigned_to_nat(0);
    v___x_1351_ = lean_nat_dec_eq(v_start_1344_, v___x_1350_);
    if v___x_1351_ == 0 {
        let mut v_root_1352_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1353_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shift_1354_: usize = 0;
        let mut v_tailOff_1355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: u8 = 0;
        v_root_1352_ = lean_ctor_get(v_t_1342_, 0);
        lean_inc_ref(v_root_1352_);
        v_tail_1353_ = lean_ctor_get(v_t_1342_, 1);
        lean_inc_ref(v_tail_1353_);
        v_shift_1354_ = lean_ctor_get_usize(v_t_1342_, 4);
        v_tailOff_1355_ = lean_ctor_get(v_t_1342_, 3);
        lean_inc(v_tailOff_1355_);
        lean_dec_ref(v_t_1342_);
        v___x_1356_ = lean_nat_dec_le(v_tailOff_1355_, v_start_1344_);
        if v___x_1356_ == 0 {
            let mut v___x_1357_: usize = 0;
            let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_tailOff_1355_);
            v___x_1357_ = lean_usize_of_nat(v_start_1344_);
            v___x_1358_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__7(v_auxDeclToFullName_1341_, v_root_1352_, v___x_1357_, v_shift_1354_, v_init_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
            if lean_obj_tag(v___x_1358_) == 0 {
                let mut v_a_1359_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1361_: u8 = 0;
                v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
                lean_inc(v_a_1359_);
                v___x_1360_ = lean_array_get_size(v_tail_1353_);
                v___x_1361_ = lean_nat_dec_lt(v___x_1350_, v___x_1360_);
                if v___x_1361_ == 0 {
                    lean_dec(v_a_1359_);
                    lean_dec_ref(v_tail_1353_);
                    return v___x_1358_;
                } else {
                    let mut v___x_1362_: u8 = 0;
                    v___x_1362_ = lean_nat_dec_le(v___x_1360_, v___x_1360_);
                    if v___x_1362_ == 0 {
                        if v___x_1361_ == 0 {
                            lean_dec(v_a_1359_);
                            lean_dec_ref(v_tail_1353_);
                            return v___x_1358_;
                        } else {
                            let mut v___x_1363_: usize = 0;
                            let mut v___x_1364_: usize = 0;
                            let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref_known(v___x_1358_, 1);
                            v___x_1363_ = 0usize;
                            v___x_1364_ = lean_usize_of_nat(v___x_1360_);
                            v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1353_, v___x_1363_, v___x_1364_, v_a_1359_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                            lean_dec_ref(v_tail_1353_);
                            return v___x_1365_;
                        }
                    } else {
                        let mut v___x_1366_: usize = 0;
                        let mut v___x_1367_: usize = 0;
                        let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_1358_, 1);
                        v___x_1366_ = 0usize;
                        v___x_1367_ = lean_usize_of_nat(v___x_1360_);
                        v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1353_, v___x_1366_, v___x_1367_, v_a_1359_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                        lean_dec_ref(v_tail_1353_);
                        return v___x_1368_;
                    }
                }
            } else {
                lean_dec_ref(v_tail_1353_);
                return v___x_1358_;
            }
        } else {
            let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1371_: u8 = 0;
            lean_dec_ref(v_root_1352_);
            v___x_1369_ = lean_nat_sub(v_start_1344_, v_tailOff_1355_);
            lean_dec(v_tailOff_1355_);
            v___x_1370_ = lean_array_get_size(v_tail_1353_);
            v___x_1371_ = lean_nat_dec_lt(v___x_1369_, v___x_1370_);
            if v___x_1371_ == 0 {
                let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_1369_);
                lean_dec_ref(v_tail_1353_);
                v___x_1372_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1372_, 0, v_init_1343_);
                return v___x_1372_;
            } else {
                let mut v___x_1373_: u8 = 0;
                v___x_1373_ = lean_nat_dec_le(v___x_1370_, v___x_1370_);
                if v___x_1373_ == 0 {
                    if v___x_1371_ == 0 {
                        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v___x_1369_);
                        lean_dec_ref(v_tail_1353_);
                        v___x_1374_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1374_, 0, v_init_1343_);
                        return v___x_1374_;
                    } else {
                        let mut v___x_1375_: usize = 0;
                        let mut v___x_1376_: usize = 0;
                        let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
                        v___x_1375_ = lean_usize_of_nat(v___x_1369_);
                        lean_dec(v___x_1369_);
                        v___x_1376_ = lean_usize_of_nat(v___x_1370_);
                        v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1353_, v___x_1375_, v___x_1376_, v_init_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                        lean_dec_ref(v_tail_1353_);
                        return v___x_1377_;
                    }
                } else {
                    let mut v___x_1378_: usize = 0;
                    let mut v___x_1379_: usize = 0;
                    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1378_ = lean_usize_of_nat(v___x_1369_);
                    lean_dec(v___x_1369_);
                    v___x_1379_ = lean_usize_of_nat(v___x_1370_);
                    v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1353_, v___x_1378_, v___x_1379_, v_init_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                    lean_dec_ref(v_tail_1353_);
                    return v___x_1380_;
                }
            }
        }
    } else {
        let mut v_root_1381_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
        v_root_1381_ = lean_ctor_get(v_t_1342_, 0);
        lean_inc_ref(v_root_1381_);
        v_tail_1382_ = lean_ctor_get(v_t_1342_, 1);
        lean_inc_ref(v_tail_1382_);
        lean_dec_ref(v_t_1342_);
        v___x_1383_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__9(v_auxDeclToFullName_1341_, v_root_1381_, v_init_1343_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
        if lean_obj_tag(v___x_1383_) == 0 {
            let mut v_a_1384_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1386_: u8 = 0;
            v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
            lean_inc(v_a_1384_);
            v___x_1385_ = lean_array_get_size(v_tail_1382_);
            v___x_1386_ = lean_nat_dec_lt(v___x_1350_, v___x_1385_);
            if v___x_1386_ == 0 {
                lean_dec(v_a_1384_);
                lean_dec_ref(v_tail_1382_);
                return v___x_1383_;
            } else {
                let mut v___x_1387_: u8 = 0;
                v___x_1387_ = lean_nat_dec_le(v___x_1385_, v___x_1385_);
                if v___x_1387_ == 0 {
                    if v___x_1386_ == 0 {
                        lean_dec(v_a_1384_);
                        lean_dec_ref(v_tail_1382_);
                        return v___x_1383_;
                    } else {
                        let mut v___x_1388_: usize = 0;
                        let mut v___x_1389_: usize = 0;
                        let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec_ref_known(v___x_1383_, 1);
                        v___x_1388_ = 0usize;
                        v___x_1389_ = lean_usize_of_nat(v___x_1385_);
                        v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1382_, v___x_1388_, v___x_1389_, v_a_1384_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                        lean_dec_ref(v_tail_1382_);
                        return v___x_1390_;
                    }
                } else {
                    let mut v___x_1391_: usize = 0;
                    let mut v___x_1392_: usize = 0;
                    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v___x_1383_, 1);
                    v___x_1391_ = 0usize;
                    v___x_1392_ = lean_usize_of_nat(v___x_1385_);
                    v___x_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5_spec__8(v_auxDeclToFullName_1341_, v_tail_1382_, v___x_1391_, v___x_1392_, v_a_1384_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
                    lean_dec_ref(v_tail_1382_);
                    return v___x_1393_;
                }
            }
        } else {
            lean_dec_ref(v_tail_1382_);
            return v___x_1383_;
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5___boxed(
    mut v_auxDeclToFullName_1394_: *mut LeanObject,
    mut v_t_1395_: *mut LeanObject,
    mut v_init_1396_: *mut LeanObject,
    mut v_start_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
    mut v___y_1401_: *mut LeanObject,
    mut v___y_1402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1403_: *mut LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_1394_, v_t_1395_, v_init_1396_, v_start_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
    lean_dec(v___y_1401_);
    lean_dec_ref(v___y_1400_);
    lean_dec(v___y_1399_);
    lean_dec_ref(v___y_1398_);
    lean_dec(v_start_1397_);
    lean_dec(v_auxDeclToFullName_1394_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(
    mut v_auxDeclToFullName_1404_: *mut LeanObject,
    mut v_lctx_1405_: *mut LeanObject,
    mut v_init_1406_: *mut LeanObject,
    mut v_start_1407_: *mut LeanObject,
    mut v___y_1408_: *mut LeanObject,
    mut v___y_1409_: *mut LeanObject,
    mut v___y_1410_: *mut LeanObject,
    mut v___y_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    v_decls_1413_ = lean_ctor_get(v_lctx_1405_, 1);
    lean_inc_ref(v_decls_1413_);
    lean_dec_ref(v_lctx_1405_);
    v___x_1414_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3_spec__5(v_auxDeclToFullName_1404_, v_decls_1413_, v_init_1406_, v_start_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
    return v___x_1414_;
}
pub unsafe fn l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3___boxed(
    mut v_auxDeclToFullName_1415_: *mut LeanObject,
    mut v_lctx_1416_: *mut LeanObject,
    mut v_init_1417_: *mut LeanObject,
    mut v_start_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_1415_, v_lctx_1416_, v_init_1417_, v_start_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
    lean_dec(v___y_1422_);
    lean_dec_ref(v___y_1421_);
    lean_dec(v___y_1420_);
    lean_dec_ref(v___y_1419_);
    lean_dec(v_start_1418_);
    lean_dec(v_auxDeclToFullName_1415_);
    return v_res_1424_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1425_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    v___x_1426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__0);
    v___x_1427_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1427_, 0, v___x_1426_);
    return v___x_1427_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1428_ = lean_unsigned_to_nat(32);
    v___x_1429_ = lean_mk_empty_array_with_capacity(v___x_1428_);
    v___x_1430_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1431_: usize = 0;
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = 5usize;
    v___x_1432_ = lean_unsigned_to_nat(0);
    v___x_1433_ = lean_unsigned_to_nat(32);
    v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
    v___x_1435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__2);
    v___x_1436_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    lean_ctor_set(v___x_1436_, 1, v___x_1434_);
    lean_ctor_set(v___x_1436_, 2, v___x_1432_);
    lean_ctor_set(v___x_1436_, 3, v___x_1432_);
    lean_ctor_set_usize(v___x_1436_, 4, v___x_1431_);
    return v___x_1436_;
}
pub unsafe fn _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ = lean_box(1);
    v___x_1438_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__3);
    v___x_1439_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__1);
    v___x_1440_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1440_, 0, v___x_1439_);
    lean_ctor_set(v___x_1440_, 1, v___x_1438_);
    lean_ctor_set(v___x_1440_, 2, v___x_1437_);
    return v___x_1440_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(
    mut v_lctx_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
    mut v___y_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_auxDeclToFullName_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v_auxDeclToFullName_1447_ = lean_ctor_get(v_lctx_1441_, 2);
    lean_inc(v_auxDeclToFullName_1447_);
    v___x_1448_ = lean_unsigned_to_nat(0);
    v___x_1449_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4_once), _init_l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___closed__4);
    v___x_1450_ = l_Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__3(v_auxDeclToFullName_1447_, v_lctx_1441_, v___x_1449_, v___x_1448_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
    lean_dec(v_auxDeclToFullName_1447_);
    return v___x_1450_;
}
pub unsafe fn l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0___boxed(
    mut v_lctx_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
    mut v___y_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1457_: *mut LeanObject = core::ptr::null_mut();
    v_res_1457_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
    lean_dec(v___y_1455_);
    lean_dec_ref(v___y_1454_);
    lean_dec(v___y_1453_);
    lean_dec_ref(v___y_1452_);
    return v_res_1457_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(
    mut v_x_1458_: *mut LeanObject,
    mut v_x_1459_: *mut LeanObject,
    mut v_x_1460_: *mut LeanObject,
    mut v_x_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1462_ = lean_ctor_get(v_x_1458_, 0);
                v_vs_1463_ = lean_ctor_get(v_x_1458_, 1);
                v_isSharedCheck_1487_ = (!lean_is_exclusive(v_x_1458_)) as u8;
                if v_isSharedCheck_1487_ == 0 {
                    v___x_1465_ = v_x_1458_;
                    v_isShared_1466_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1463_);
                    lean_inc(v_ks_1462_);
                    lean_dec(v_x_1458_);
                    v___x_1465_ = lean_box(0);
                    v_isShared_1466_ = v_isSharedCheck_1487_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1467_ = lean_array_get_size(v_ks_1462_);
                v___x_1468_ = lean_nat_dec_lt(v_x_1459_, v___x_1467_);
                if v___x_1468_ == 0 {
                    lean_dec(v_x_1459_);
                    v___x_1469_ = lean_array_push(v_ks_1462_, v_x_1460_);
                    v___x_1470_ = lean_array_push(v_vs_1463_, v_x_1461_);
                    if v_isShared_1466_ == 0 {
                        lean_ctor_set(v___x_1465_, 1, v___x_1470_);
                        lean_ctor_set(v___x_1465_, 0, v___x_1469_);
                        v___x_1472_ = v___x_1465_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1469_);
                        lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
                        v___x_1472_ = v_reuseFailAlloc_1473_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1474_ = lean_array_fget_borrowed(v_ks_1462_, v_x_1459_);
                    v___x_1475_ = l_Lean_instBEqMVarId_beq(v_x_1460_, v_k_x27_1474_);
                    if v___x_1475_ == 0 {
                        if v_isShared_1466_ == 0 {
                            v___x_1477_ = v___x_1465_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_ks_1462_);
                            lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_vs_1463_);
                            v___x_1477_ = v_reuseFailAlloc_1481_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1482_ = lean_array_fset(v_ks_1462_, v_x_1459_, v_x_1460_);
                        v___x_1483_ = lean_array_fset(v_vs_1463_, v_x_1459_, v_x_1461_);
                        lean_dec(v_x_1459_);
                        if v_isShared_1466_ == 0 {
                            lean_ctor_set(v___x_1465_, 1, v___x_1483_);
                            lean_ctor_set(v___x_1465_, 0, v___x_1482_);
                            v___x_1485_ = v___x_1465_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1482_);
                            lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1483_);
                            v___x_1485_ = v_reuseFailAlloc_1486_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1472_;
            }
            3 => {
                v___x_1478_ = lean_unsigned_to_nat(1);
                v___x_1479_ = lean_nat_add(v_x_1459_, v___x_1478_);
                lean_dec(v_x_1459_);
                v_x_1458_ = v___x_1477_;
                v_x_1459_ = v___x_1479_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(
    mut v_n_1488_: *mut LeanObject,
    mut v_k_1489_: *mut LeanObject,
    mut v_v_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1491_ = lean_unsigned_to_nat(0);
    v___x_1492_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_n_1488_, v___x_1491_, v_k_1489_, v_v_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_1493_: usize = 0;
    let mut v___x_1494_: usize = 0;
    let mut v___x_1495_: usize = 0;
    v___x_1493_ = 5usize;
    v___x_1494_ = 1usize;
    v___x_1495_ = lean_usize_shift_left(v___x_1494_, v___x_1493_);
    return v___x_1495_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_1496_: usize = 0;
    let mut v___x_1497_: usize = 0;
    let mut v___x_1498_: usize = 0;
    v___x_1496_ = 1usize;
    v___x_1497_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__0);
    v___x_1498_ = lean_usize_sub(v___x_1497_, v___x_1496_);
    return v___x_1498_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1499_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(
    mut v_x_1500_: *mut LeanObject,
    mut v_x_1501_: usize,
    mut v_x_1502_: usize,
    mut v_x_1503_: *mut LeanObject,
    mut v_x_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: usize = 0;
    let mut v___x_1507_: usize = 0;
    let mut v___x_1508_: usize = 0;
    let mut v___x_1509_: usize = 0;
    let mut v_j_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1515_: u8 = 0;
    let mut v_v_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1536_: u8 = 0;
    let mut v_node_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1540_: u8 = 0;
    let mut v___x_1541_: usize = 0;
    let mut v___x_1542_: usize = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1547_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut v_unused_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1560_: u8 = 0;
    let mut v_ks_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1500_) == 0 {
                    v_es_1505_ = lean_ctor_get(v_x_1500_, 0);
                    v___x_1506_ = 5usize;
                    v___x_1507_ = 1usize;
                    v___x_1508_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__1);
                    v___x_1509_ = lean_usize_land(v_x_1501_, v___x_1508_);
                    v_j_1510_ = lean_usize_to_nat(v___x_1509_);
                    v___x_1511_ = lean_array_get_size(v_es_1505_);
                    v___x_1512_ = lean_nat_dec_lt(v_j_1510_, v___x_1511_);
                    if v___x_1512_ == 0 {
                        lean_dec(v_j_1510_);
                        lean_dec(v_x_1504_);
                        lean_dec(v_x_1503_);
                        return v_x_1500_;
                    } else {
                        lean_inc_ref(v_es_1505_);
                        v_isSharedCheck_1549_ = (!lean_is_exclusive(v_x_1500_)) as u8;
                        if v_isSharedCheck_1549_ == 0 {
                            v_unused_1550_ = lean_ctor_get(v_x_1500_, 0);
                            lean_dec(v_unused_1550_);
                            v___x_1514_ = v_x_1500_;
                            v_isShared_1515_ = v_isSharedCheck_1549_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1500_);
                            v___x_1514_ = lean_box(0);
                            v_isShared_1515_ = v_isSharedCheck_1549_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1551_ = lean_ctor_get(v_x_1500_, 0);
                    v_vs_1552_ = lean_ctor_get(v_x_1500_, 1);
                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v_x_1500_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1554_ = v_x_1500_;
                        v_isShared_1555_ = v_isSharedCheck_1572_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1552_);
                        lean_inc(v_ks_1551_);
                        lean_dec(v_x_1500_);
                        v___x_1554_ = lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1572_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1516_ = lean_array_fget(v_es_1505_, v_j_1510_);
                v___x_1517_ = lean_box(0);
                v_xs_x27_1518_ = lean_array_fset(v_es_1505_, v_j_1510_, v___x_1517_);
                match lean_obj_tag(v_v_1516_) {
                    0 => {
                        v_key_1525_ = lean_ctor_get(v_v_1516_, 0);
                        v_val_1526_ = lean_ctor_get(v_v_1516_, 1);
                        v_isSharedCheck_1536_ = (!lean_is_exclusive(v_v_1516_)) as u8;
                        if v_isSharedCheck_1536_ == 0 {
                            v___x_1528_ = v_v_1516_;
                            v_isShared_1529_ = v_isSharedCheck_1536_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1526_);
                            lean_inc(v_key_1525_);
                            lean_dec(v_v_1516_);
                            v___x_1528_ = lean_box(0);
                            v_isShared_1529_ = v_isSharedCheck_1536_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1537_ = lean_ctor_get(v_v_1516_, 0);
                        v_isSharedCheck_1547_ = (!lean_is_exclusive(v_v_1516_)) as u8;
                        if v_isSharedCheck_1547_ == 0 {
                            v___x_1539_ = v_v_1516_;
                            v_isShared_1540_ = v_isSharedCheck_1547_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1537_);
                            lean_dec(v_v_1516_);
                            v___x_1539_ = lean_box(0);
                            v_isShared_1540_ = v_isSharedCheck_1547_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1548_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1548_, 0, v_x_1503_);
                        lean_ctor_set(v___x_1548_, 1, v_x_1504_);
                        v___y_1520_ = v___x_1548_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1521_ = lean_array_fset(v_xs_x27_1518_, v_j_1510_, v___y_1520_);
                lean_dec(v_j_1510_);
                if v_isShared_1515_ == 0 {
                    lean_ctor_set(v___x_1514_, 0, v___x_1521_);
                    v___x_1523_ = v___x_1514_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
                    v___x_1523_ = v_reuseFailAlloc_1524_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1523_;
            }
            4 => {
                v___x_1530_ = l_Lean_instBEqMVarId_beq(v_x_1503_, v_key_1525_);
                if v___x_1530_ == 0 {
                    lean_del_object(v___x_1528_);
                    v___x_1531_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1525_,
                        v_val_1526_,
                        v_x_1503_,
                        v_x_1504_,
                    );
                    v___x_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                    v___y_1520_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1526_);
                    lean_dec(v_key_1525_);
                    if v_isShared_1529_ == 0 {
                        lean_ctor_set(v___x_1528_, 1, v_x_1504_);
                        lean_ctor_set(v___x_1528_, 0, v_x_1503_);
                        v___x_1534_ = v___x_1528_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_x_1503_);
                        lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_x_1504_);
                        v___x_1534_ = v_reuseFailAlloc_1535_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1520_ = v___x_1534_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1541_ = lean_usize_shift_right(v_x_1501_, v___x_1506_);
                v___x_1542_ = lean_usize_add(v_x_1502_, v___x_1507_);
                v___x_1543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_node_1537_, v___x_1541_, v___x_1542_, v_x_1503_, v_x_1504_);
                if v_isShared_1540_ == 0 {
                    lean_ctor_set(v___x_1539_, 0, v___x_1543_);
                    v___x_1545_ = v___x_1539_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
                    v___x_1545_ = v_reuseFailAlloc_1546_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1520_ = v___x_1545_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1555_ == 0 {
                    v___x_1557_ = v___x_1554_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_ks_1551_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_vs_1552_);
                    v___x_1557_ = v_reuseFailAlloc_1571_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1558_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v___x_1557_, v_x_1503_, v_x_1504_);
                v___x_1566_ = 7usize;
                v___x_1567_ = lean_usize_dec_le(v___x_1566_, v_x_1502_);
                if v___x_1567_ == 0 {
                    v___x_1568_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1558_);
                    v___x_1569_ = lean_unsigned_to_nat(4);
                    v___x_1570_ = lean_nat_dec_lt(v___x_1568_, v___x_1569_);
                    lean_dec(v___x_1568_);
                    v___y_1560_ = v___x_1570_;
                    state = 10;
                    continue;
                } else {
                    v___y_1560_ = v___x_1567_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1560_ == 0 {
                    v_ks_1561_ = lean_ctor_get(v_newNode_1558_, 0);
                    lean_inc_ref(v_ks_1561_);
                    v_vs_1562_ = lean_ctor_get(v_newNode_1558_, 1);
                    lean_inc_ref(v_vs_1562_);
                    lean_dec_ref(v_newNode_1558_);
                    v___x_1563_ = lean_unsigned_to_nat(0);
                    v___x_1564_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___closed__2);
                    v___x_1565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_x_1502_, v_ks_1561_, v_vs_1562_, v___x_1563_, v___x_1564_);
                    lean_dec_ref(v_vs_1562_);
                    lean_dec_ref(v_ks_1561_);
                    return v___x_1565_;
                } else {
                    return v_newNode_1558_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(
    mut v_depth_1573_: usize,
    mut v_keys_1574_: *mut LeanObject,
    mut v_vals_1575_: *mut LeanObject,
    mut v_i_1576_: *mut LeanObject,
    mut v_entries_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v_k_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: u64 = 0;
    let mut v_h_1583_: usize = 0;
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: usize = 0;
    let mut v___x_1587_: usize = 0;
    let mut v___x_1588_: usize = 0;
    let mut v_h_1589_: usize = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1578_ = lean_array_get_size(v_keys_1574_);
                v___x_1579_ = lean_nat_dec_lt(v_i_1576_, v___x_1578_);
                if v___x_1579_ == 0 {
                    lean_dec(v_i_1576_);
                    return v_entries_1577_;
                } else {
                    v_k_1580_ = lean_array_fget_borrowed(v_keys_1574_, v_i_1576_);
                    v_v_1581_ = lean_array_fget_borrowed(v_vals_1575_, v_i_1576_);
                    v___x_1582_ = l_Lean_instHashableMVarId_hash(v_k_1580_);
                    v_h_1583_ = lean_uint64_to_usize(v___x_1582_);
                    v___x_1584_ = 5usize;
                    v___x_1585_ = lean_unsigned_to_nat(1);
                    v___x_1586_ = 1usize;
                    v___x_1587_ = lean_usize_sub(v_depth_1573_, v___x_1586_);
                    v___x_1588_ = lean_usize_mul(v___x_1584_, v___x_1587_);
                    v_h_1589_ = lean_usize_shift_right(v_h_1583_, v___x_1588_);
                    v___x_1590_ = lean_nat_add(v_i_1576_, v___x_1585_);
                    lean_dec(v_i_1576_);
                    lean_inc(v_v_1581_);
                    lean_inc(v_k_1580_);
                    v___x_1591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_entries_1577_, v_h_1589_, v_depth_1573_, v_k_1580_, v_v_1581_);
                    v_i_1576_ = v___x_1590_;
                    v_entries_1577_ = v___x_1591_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg___boxed(
    mut v_depth_1593_: *mut LeanObject,
    mut v_keys_1594_: *mut LeanObject,
    mut v_vals_1595_: *mut LeanObject,
    mut v_i_1596_: *mut LeanObject,
    mut v_entries_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1598_: usize = 0;
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1598_ = lean_unbox_usize(v_depth_1593_);
    lean_dec(v_depth_1593_);
    v_res_1599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_boxed_1598_, v_keys_1594_, v_vals_1595_, v_i_1596_, v_entries_1597_);
    lean_dec_ref(v_vals_1595_);
    lean_dec_ref(v_keys_1594_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_x_1600_: *mut LeanObject,
    mut v_x_1601_: *mut LeanObject,
    mut v_x_1602_: *mut LeanObject,
    mut v_x_1603_: *mut LeanObject,
    mut v_x_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6138__boxed_1605_: usize = 0;
    let mut v_x_6139__boxed_1606_: usize = 0;
    let mut v_res_1607_: *mut LeanObject = core::ptr::null_mut();
    v_x_6138__boxed_1605_ = lean_unbox_usize(v_x_1601_);
    lean_dec(v_x_1601_);
    v_x_6139__boxed_1606_ = lean_unbox_usize(v_x_1602_);
    lean_dec(v_x_1602_);
    v_res_1607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_1600_, v_x_6138__boxed_1605_, v_x_6139__boxed_1606_, v_x_1603_, v_x_1604_);
    return v_res_1607_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(
    mut v_x_1608_: *mut LeanObject,
    mut v_x_1609_: *mut LeanObject,
    mut v_x_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1611_: u64 = 0;
    let mut v___x_1612_: usize = 0;
    let mut v___x_1613_: usize = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    v___x_1611_ = l_Lean_instHashableMVarId_hash(v_x_1609_);
    v___x_1612_ = lean_uint64_to_usize(v___x_1611_);
    v___x_1613_ = 1usize;
    v___x_1614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_1608_, v___x_1612_, v___x_1613_, v_x_1609_, v_x_1610_);
    return v___x_1614_;
}
pub unsafe fn l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(
    mut v_mvarId_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarDecl_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_depth_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1629_: u8 = 0;
    let mut v_numScopeArgs_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v_depth_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1667_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_isSharedCheck_1685_: u8 = 0;
    let mut v_a_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = lean_st_ref_get(v___y_1617_);
                v_mctx_1622_ = lean_ctor_get(v___x_1621_, 0);
                lean_inc_ref(v_mctx_1622_);
                lean_dec(v___x_1621_);
                lean_inc(v_mvarId_1615_);
                v_mvarDecl_1623_ = l_Lean_MetavarContext_getDecl(v_mctx_1622_, v_mvarId_1615_);
                lean_dec_ref(v_mctx_1622_);
                v_userName_1624_ = lean_ctor_get(v_mvarDecl_1623_, 0);
                v_lctx_1625_ = lean_ctor_get(v_mvarDecl_1623_, 1);
                v_type_1626_ = lean_ctor_get(v_mvarDecl_1623_, 2);
                v_depth_1627_ = lean_ctor_get(v_mvarDecl_1623_, 3);
                v_localInstances_1628_ = lean_ctor_get(v_mvarDecl_1623_, 4);
                v_kind_1629_ = lean_ctor_get_uint8(
                    v_mvarDecl_1623_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_numScopeArgs_1630_ = lean_ctor_get(v_mvarDecl_1623_, 5);
                v_index_1631_ = lean_ctor_get(v_mvarDecl_1623_, 6);
                v_isSharedCheck_1694_ = (!lean_is_exclusive(v_mvarDecl_1623_)) as u8;
                if v_isSharedCheck_1694_ == 0 {
                    v___x_1633_ = v_mvarDecl_1623_;
                    v_isShared_1634_ = v_isSharedCheck_1694_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_index_1631_);
                    lean_inc(v_numScopeArgs_1630_);
                    lean_inc(v_localInstances_1628_);
                    lean_inc(v_depth_1627_);
                    lean_inc(v_type_1626_);
                    lean_inc(v_lctx_1625_);
                    lean_inc(v_userName_1624_);
                    lean_dec(v_mvarDecl_1623_);
                    v___x_1633_ = lean_box(0);
                    v_isShared_1634_ = v_isSharedCheck_1694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1635_ = l_Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0(v_lctx_1625_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
                if lean_obj_tag(v___x_1635_) == 0 {
                    v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
                    lean_inc(v_a_1636_);
                    lean_dec_ref_known(v___x_1635_, 1);
                    v___x_1637_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_type_1626_, v___y_1617_);
                    v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
                    v_isSharedCheck_1685_ = (!lean_is_exclusive(v___x_1637_)) as u8;
                    if v_isSharedCheck_1685_ == 0 {
                        v___x_1640_ = v___x_1637_;
                        v_isShared_1641_ = v_isSharedCheck_1685_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1638_);
                        lean_dec(v___x_1637_);
                        v___x_1640_ = lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1685_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1633_);
                    lean_dec(v_index_1631_);
                    lean_dec(v_numScopeArgs_1630_);
                    lean_dec_ref(v_localInstances_1628_);
                    lean_dec(v_depth_1627_);
                    lean_dec_ref(v_type_1626_);
                    lean_dec(v_userName_1624_);
                    lean_dec(v_mvarId_1615_);
                    v_a_1686_ = lean_ctor_get(v___x_1635_, 0);
                    v_isSharedCheck_1693_ = (!lean_is_exclusive(v___x_1635_)) as u8;
                    if v_isSharedCheck_1693_ == 0 {
                        v___x_1688_ = v___x_1635_;
                        v_isShared_1689_ = v_isSharedCheck_1693_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1686_);
                        lean_dec(v___x_1635_);
                        v___x_1688_ = lean_box(0);
                        v_isShared_1689_ = v_isSharedCheck_1693_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1642_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1642_, 0, v_a_1636_);
                lean_ctor_set(v___x_1642_, 1, v_a_1638_);
                v___x_1643_ = lean_sharecommon_quick(v___x_1642_);
                lean_dec_ref_known(v___x_1642_, 2);
                v_fst_1644_ = lean_ctor_get(v___x_1643_, 0);
                lean_inc(v_fst_1644_);
                v_snd_1645_ = lean_ctor_get(v___x_1643_, 1);
                lean_inc(v_snd_1645_);
                lean_dec(v___x_1643_);
                v___x_1646_ = lean_st_ref_take(v___y_1617_);
                v_mctx_1647_ = lean_ctor_get(v___x_1646_, 0);
                v_cache_1648_ = lean_ctor_get(v___x_1646_, 1);
                v_zetaDeltaFVarIds_1649_ = lean_ctor_get(v___x_1646_, 2);
                v_postponed_1650_ = lean_ctor_get(v___x_1646_, 3);
                v_diag_1651_ = lean_ctor_get(v___x_1646_, 4);
                v_isSharedCheck_1684_ = (!lean_is_exclusive(v___x_1646_)) as u8;
                if v_isSharedCheck_1684_ == 0 {
                    v___x_1653_ = v___x_1646_;
                    v_isShared_1654_ = v_isSharedCheck_1684_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1651_);
                    lean_inc(v_postponed_1650_);
                    lean_inc(v_zetaDeltaFVarIds_1649_);
                    lean_inc(v_cache_1648_);
                    lean_inc(v_mctx_1647_);
                    lean_dec(v___x_1646_);
                    v___x_1653_ = lean_box(0);
                    v_isShared_1654_ = v_isSharedCheck_1684_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_depth_1655_ = lean_ctor_get(v_mctx_1647_, 0);
                v_levelAssignDepth_1656_ = lean_ctor_get(v_mctx_1647_, 1);
                v_lmvarCounter_1657_ = lean_ctor_get(v_mctx_1647_, 2);
                v_mvarCounter_1658_ = lean_ctor_get(v_mctx_1647_, 3);
                v_lDecls_1659_ = lean_ctor_get(v_mctx_1647_, 4);
                v_decls_1660_ = lean_ctor_get(v_mctx_1647_, 5);
                v_userNames_1661_ = lean_ctor_get(v_mctx_1647_, 6);
                v_lAssignment_1662_ = lean_ctor_get(v_mctx_1647_, 7);
                v_eAssignment_1663_ = lean_ctor_get(v_mctx_1647_, 8);
                v_dAssignment_1664_ = lean_ctor_get(v_mctx_1647_, 9);
                v_isSharedCheck_1683_ = (!lean_is_exclusive(v_mctx_1647_)) as u8;
                if v_isSharedCheck_1683_ == 0 {
                    v___x_1666_ = v_mctx_1647_;
                    v_isShared_1667_ = v_isSharedCheck_1683_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1664_);
                    lean_inc(v_eAssignment_1663_);
                    lean_inc(v_lAssignment_1662_);
                    lean_inc(v_userNames_1661_);
                    lean_inc(v_decls_1660_);
                    lean_inc(v_lDecls_1659_);
                    lean_inc(v_mvarCounter_1658_);
                    lean_inc(v_lmvarCounter_1657_);
                    lean_inc(v_levelAssignDepth_1656_);
                    lean_inc(v_depth_1655_);
                    lean_dec(v_mctx_1647_);
                    v___x_1666_ = lean_box(0);
                    v_isShared_1667_ = v_isSharedCheck_1683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1634_ == 0 {
                    lean_ctor_set(v___x_1633_, 2, v_snd_1645_);
                    lean_ctor_set(v___x_1633_, 1, v_fst_1644_);
                    v___x_1669_ = v___x_1633_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_userName_1624_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_fst_1644_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_snd_1645_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_depth_1627_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_localInstances_1628_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 5, v_numScopeArgs_1630_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 6, v_index_1631_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1682_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_kind_1629_,
                    );
                    v___x_1669_ = v_reuseFailAlloc_1682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1670_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_decls_1660_, v_mvarId_1615_, v___x_1669_);
                if v_isShared_1667_ == 0 {
                    lean_ctor_set(v___x_1666_, 5, v___x_1670_);
                    v___x_1672_ = v___x_1666_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_depth_1655_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_levelAssignDepth_1656_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_lmvarCounter_1657_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_mvarCounter_1658_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_lDecls_1659_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 5, v___x_1670_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_userNames_1661_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 7, v_lAssignment_1662_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 8, v_eAssignment_1663_);
                    lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_dAssignment_1664_);
                    v___x_1672_ = v_reuseFailAlloc_1681_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1654_ == 0 {
                    lean_ctor_set(v___x_1653_, 0, v___x_1672_);
                    v___x_1674_ = v___x_1653_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1672_);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_cache_1648_);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 2, v_zetaDeltaFVarIds_1649_);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_postponed_1650_);
                    lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_diag_1651_);
                    v___x_1674_ = v_reuseFailAlloc_1680_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1675_ = lean_st_ref_set(v___y_1617_, v___x_1674_);
                v___x_1676_ = lean_box(0);
                if v_isShared_1641_ == 0 {
                    lean_ctor_set(v___x_1640_, 0, v___x_1676_);
                    v___x_1678_ = v___x_1640_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
                    v___x_1678_ = v_reuseFailAlloc_1679_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1678_;
            }
            9 => {
                if v_isShared_1689_ == 0 {
                    v___x_1691_ = v___x_1688_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
                    v___x_1691_ = v_reuseFailAlloc_1692_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0___boxed(
    mut v_mvarId_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1701_: *mut LeanObject = core::ptr::null_mut();
    v_res_1701_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(
        v_mvarId_1695_,
        v___y_1696_,
        v___y_1697_,
        v___y_1698_,
        v___y_1699_,
    );
    lean_dec(v___y_1699_);
    lean_dec_ref(v___y_1698_);
    lean_dec(v___y_1697_);
    lean_dec_ref(v___y_1696_);
    return v_res_1701_;
}
pub unsafe fn l_Lean_Elab_runTactic(
    mut v_mvarId_1702_: *mut LeanObject,
    mut v_tacticCode_1703_: *mut LeanObject,
    mut v_ctx_1704_: *mut LeanObject,
    mut v_s_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
    mut v_a_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v_a_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_1702_);
                v___x_1711_ = l_Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0(
                    v_mvarId_1702_,
                    v_a_1706_,
                    v_a_1707_,
                    v_a_1708_,
                    v_a_1709_,
                );
                if lean_obj_tag(v___x_1711_) == 0 {
                    lean_dec_ref_known(v___x_1711_, 1);
                    v___f_1712_ = lean_alloc_closure(
                        l_Lean_Elab_runTactic___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_1712_, 0, v_tacticCode_1703_);
                    v___x_1713_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_1713_, 0, v_mvarId_1702_);
                    lean_closure_set(v___x_1713_, 1, v___f_1712_);
                    v___x_1714_ = 1;
                    v___x_1715_ = lean_box((v___x_1714_) as usize);
                    v___f_1716_ = lean_alloc_closure(
                        l_Lean_Elab_runTactic___lam__1___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___f_1716_, 0, v___x_1713_);
                    lean_closure_set(v___f_1716_, 1, v___x_1715_);
                    v___x_1717_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                        v___f_1716_,
                        v_ctx_1704_,
                        v_s_1705_,
                        v_a_1706_,
                        v_a_1707_,
                        v_a_1708_,
                        v_a_1709_,
                    );
                    return v___x_1717_;
                } else {
                    lean_dec_ref(v_s_1705_);
                    lean_dec_ref(v_ctx_1704_);
                    lean_dec(v_tacticCode_1703_);
                    lean_dec(v_mvarId_1702_);
                    v_a_1718_ = lean_ctor_get(v___x_1711_, 0);
                    v_isSharedCheck_1725_ = (!lean_is_exclusive(v___x_1711_)) as u8;
                    if v_isSharedCheck_1725_ == 0 {
                        v___x_1720_ = v___x_1711_;
                        v_isShared_1721_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1718_);
                        lean_dec(v___x_1711_);
                        v___x_1720_ = lean_box(0);
                        v_isShared_1721_ = v_isSharedCheck_1725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1721_ == 0 {
                    v___x_1723_ = v___x_1720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_runTactic___boxed(
    mut v_mvarId_1726_: *mut LeanObject,
    mut v_tacticCode_1727_: *mut LeanObject,
    mut v_ctx_1728_: *mut LeanObject,
    mut v_s_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_a_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1735_: *mut LeanObject = core::ptr::null_mut();
    v_res_1735_ = l_Lean_Elab_runTactic(
        v_mvarId_1726_,
        v_tacticCode_1727_,
        v_ctx_1728_,
        v_s_1729_,
        v_a_1730_,
        v_a_1731_,
        v_a_1732_,
        v_a_1733_,
    );
    lean_dec(v_a_1733_);
    lean_dec_ref(v_a_1732_);
    lean_dec(v_a_1731_);
    lean_dec_ref(v_a_1730_);
    return v_res_1735_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(
    mut v_e_1736_: *mut LeanObject,
    mut v___y_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___redArg(v_e_1736_, v___y_1738_);
    return v___x_1742_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1___boxed(
    mut v_e_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1749_: *mut LeanObject = core::ptr::null_mut();
    v_res_1749_ = l_Lean_instantiateMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__1(v_e_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
    lean_dec(v___y_1747_);
    lean_dec_ref(v___y_1746_);
    lean_dec(v___y_1745_);
    lean_dec_ref(v___y_1744_);
    return v_res_1749_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2(
    mut v_00_u03b2_1750_: *mut LeanObject,
    mut v_x_1751_: *mut LeanObject,
    mut v_x_1752_: *mut LeanObject,
    mut v_x_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2___redArg(v_x_1751_, v_x_1752_, v_x_1753_);
    return v___x_1754_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(
    mut v_00_u03b4_1755_: *mut LeanObject,
    mut v_t_1756_: *mut LeanObject,
    mut v_k_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v___x_1758_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___redArg(v_t_1756_, v_k_1757_);
    return v___x_1758_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b4_1759_: *mut LeanObject,
    mut v_t_1760_: *mut LeanObject,
    mut v_k_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__0_spec__1(v_00_u03b4_1759_, v_t_1760_, v_k_1761_);
    lean_dec(v_k_1761_);
    lean_dec(v_t_1760_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1763_: *mut LeanObject,
    mut v_x_1764_: *mut LeanObject,
    mut v_x_1765_: usize,
    mut v_x_1766_: usize,
    mut v_x_1767_: *mut LeanObject,
    mut v_x_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1769_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___redArg(v_x_1764_, v_x_1765_, v_x_1766_, v_x_1767_, v_x_1768_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1770_: *mut LeanObject,
    mut v_x_1771_: *mut LeanObject,
    mut v_x_1772_: *mut LeanObject,
    mut v_x_1773_: *mut LeanObject,
    mut v_x_1774_: *mut LeanObject,
    mut v_x_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6489__boxed_1776_: usize = 0;
    let mut v_x_6490__boxed_1777_: usize = 0;
    let mut v_res_1778_: *mut LeanObject = core::ptr::null_mut();
    v_x_6489__boxed_1776_ = lean_unbox_usize(v_x_1772_);
    lean_dec(v_x_1772_);
    v_x_6490__boxed_1777_ = lean_unbox_usize(v_x_1773_);
    lean_dec(v_x_1773_);
    v_res_1778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6(v_00_u03b2_1770_, v_x_1771_, v_x_6489__boxed_1776_, v_x_6490__boxed_1777_, v_x_1774_, v_x_1775_);
    return v_res_1778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8(
    mut v_00_u03b2_1779_: *mut LeanObject,
    mut v_n_1780_: *mut LeanObject,
    mut v_k_1781_: *mut LeanObject,
    mut v_v_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8___redArg(v_n_1780_, v_k_1781_, v_v_1782_);
    return v___x_1783_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(
    mut v_00_u03b2_1784_: *mut LeanObject,
    mut v_depth_1785_: usize,
    mut v_keys_1786_: *mut LeanObject,
    mut v_vals_1787_: *mut LeanObject,
    mut v_heq_1788_: *mut LeanObject,
    mut v_i_1789_: *mut LeanObject,
    mut v_entries_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    v___x_1791_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___redArg(v_depth_1785_, v_keys_1786_, v_vals_1787_, v_i_1789_, v_entries_1790_);
    return v___x_1791_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9___boxed(
    mut v_00_u03b2_1792_: *mut LeanObject,
    mut v_depth_1793_: *mut LeanObject,
    mut v_keys_1794_: *mut LeanObject,
    mut v_vals_1795_: *mut LeanObject,
    mut v_heq_1796_: *mut LeanObject,
    mut v_i_1797_: *mut LeanObject,
    mut v_entries_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1799_: usize = 0;
    let mut v_res_1800_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1799_ = lean_unbox_usize(v_depth_1793_);
    lean_dec(v_depth_1793_);
    v_res_1800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_1792_, v_depth_boxed_1799_, v_keys_1794_, v_vals_1795_, v_heq_1796_, v_i_1797_, v_entries_1798_);
    lean_dec_ref(v_vals_1795_);
    lean_dec_ref(v_keys_1794_);
    return v_res_1800_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12(
    mut v_00_u03b2_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
    mut v_x_1803_: *mut LeanObject,
    mut v_x_1804_: *mut LeanObject,
    mut v_x_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_instantiateMVarDeclMVars___at___00Lean_Elab_runTactic_spec__0_spec__2_spec__6_spec__8_spec__12___redArg(v_x_1802_, v_x_1803_, v_x_1804_, v_x_1805_);
    return v___x_1806_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Meta(builtin);
}
